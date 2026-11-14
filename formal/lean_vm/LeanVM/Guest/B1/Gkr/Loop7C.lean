/-
  LeanVM.Guest.B1.Gkr.Loop7C

  `verify_bus_gkr_loop0`, completely: on a memory holding a layer's slot, its step's words, its
  round records and the next slot, an iteration's honest valuation satisfies its body, region by
  region.
-/

module

public import LeanVM.Guest.B1.Gkr.LayerStep
public import LeanVM.Guest.B1.Gkr.EvalC
public import LeanVM.Guest.B1.Gkr.RecsC
public import LeanVM.Guest.B1.Gkr.SpecInv
public import LeanVM.Guest.B1.Gkr.Loop29Complete
public import LeanVM.Guest.B1.Sumcheck.Gkr
public import LeanVM.Guest.Data.NameStrings

/-!
# `verify_bus_gkr_loop0`, completely (G:1996-2040)

An iteration at `x = g^j` from the slot of `L = 2j + 2 - sh` (`GkSlot`, the slot's words, nothing
waiting) runs one step of two levels (`GkStepD`, read back from the walk by `gkrStep_invT`). On a
memory holding the slot, the step's words at the cursor, the round records (`RecsAt`) and the
next slot, the body evaluated forward (`lyEvL`, its `ite`'s branches in order) holds region by
region (`lyR1 .. lyR6`):

* `lyc_head`: the combiner's permutation, the first record stored, `half = g^(k/4)` and
  `parity = g^(k % 4)`, `k = j + 1 - sh` the layer index;
* `lyc_rounds`: `verify_bus_gkr_loop0_loop0`, `gkr_rounds__L{2r}` at `r = k % 4` (a dispatch),
  `gkr_rounds__L1` at an odd depth;
* `lyc_last`: the last record read;
* `lyc_children`: the twelve children read and absorbed, four at a permutation;
* `lyc_check`: the last claim read and checked, the two new coordinates;
* `lyc_stores`: the next slot stored (`half`, `parity` through the table `k_mod_next`) and the
  next iteration called.

`Loop7Complete` assembles them (`ly_iter`, `ly_complete`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

theorem capOf_getD (S : KeccakState) {k : ℕ} (hk : k < 5) :
    (capOf S).getD k 0 = cellsOfState S false ⟨8 + k, by omega⟩ := by
  interval_cases k <;> rfl

theorem tbCapAt_getD {rd : Reader} {rec : E} {off stride : ℕ} {cap : List E}
    (h : TbCapAt rd rec off stride cap) {k : ℕ} (hk : k < 5) :
    LoadHolds rd rec (off + k * stride) (cap.getD k 0) := by
  have := h.2 k (by rw [h.1]; exact hk)
  rwa [List.getD_eq_getElem _ _ (by rw [h.1]; exact hk)]

/-- Blocks indexed by `i < n`, flattened: each one's statements. -/
theorem forall_flatten_range {P : Stmt → Prop} {n : ℕ} {g : ℕ → List Stmt}
    (h : ∀ i < n, ∀ s ∈ g i, P s) : ∀ s ∈ ((List.range n).map g).flatten, P s := by
  intro s hs
  obtain ⟨l, hl, hs⟩ := List.mem_flatten.mp hs
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
  exact h i (List.mem_range.mp hi) s hs

/-! ## The evaluation list and the regions -/

/-- `verify_bus_gkr_loop0`'s evaluation list: its body, its `ite`'s branches in order. -/
noncomputable def lyEvL : List Stmt := flatIte lyPre

theorem ly_chk : (chk 10 lyEvL).isSome = true := by decide +kernel

/-- `verify_bus_gkr_loop0`'s stores. -/
noncomputable def lyS : List Atom := storesOf 10 lyEvL

/-- The head: the slot's pointer, the combiner, the first record, `half`, `parity`. -/
def lyR1 : List Stmt :=
  [.atom (.mul (.n 10) (.n 0) (.n 0)), .atom (.mul (.n 11) (.n 10) (.n 2)),
    .atom (.mul (.n 12) (.n 11) (.n 11)), .atom (.mul (.n 13) (.n 12) (.n 11)),
    .atom (.mul (.n 14) (.n 13) (.n 13)), .atom (.mul (.n 15) (.n 14) (.n 14)),
    .atom (.mul (.n 16) (.n 15) (.n 11)), .atom (.mul (.n 17) (.n 3) (.n 16))] ++
  (List.range 6).map (fun k ↦ .atom (.load (.n (18 + k)) (.n 17) k)) ++
  [.atom (.const (.n 24) (word 1 0)), .atom (.const (.n 25) (word 0 0)),
    .atom (.const (.n 26) (word 0 0)), .atom (.const (.n 27) (word 0 0)),
    .atom (.const (.n 28) (word 0 0)),
    keccakA ([.n 25, .n 25, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28] ++
      (List.range 5).map fun k ↦ .n (18 + k)) (lyOuts 29)] ++
  challengeT (.n 29) 42 ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (43 + k)) (.n 17) (6 + k))) ++
  [.atom (.mul (.n 48) (.n 5) (.n 47))] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (37 + k)) (.n 48) (862 * k))) ++
  [.atom (.load (.n 23) (.n 48) 4310), .atom (.mul (.n 49) (.n 42) (.n 45)),
    .atom (.add (.n 50) (.n 44) (.n 49)), .atom (.mul (.n 51) (.n 42) (.n 50)),
    .atom (.add (.n 52) (.n 43) (.n 51)), .atom (.load (.n 52) (.n 48) 5172),
    .atom (.load (.n 53) (.n 17) 11), .atom (.load (.n 54) (.n 17) 12),
    .atom (.const (.n 55) (word 1 0)), .atom (.add (.n 56) (.n 55) (.n 53)),
    .atom (.const (.n 57) (word 1 0))]

/-- The rounds. -/
def lyR2 : List Stmt :=
  [.callIf (.n 56) name% «verify_bus_gkr_loop0_loop0» [.n 57, .n 53, .n 48, .n 46, .n 4],
    .atom (.mul (.n 58) (.n 53) (.n 53)), .atom (.mul (.n 59) (.n 58) (.n 58)),
    .atom (.mul (.n 60) (.n 59) (.n 59)), .atom (.mul (.n 61) (.n 48) (.n 60)),
    .atom (.mul (.n 62) (.n 46) (.n 60)),
    .dispatch (.n 54) ["gkr_rounds__L0", "gkr_rounds__L2", "gkr_rounds__L4", "gkr_rounds__L6"]
      [.n 61, .n 62, .n 4] [.n 63],
    .atom (.const (.n 64) (word 1 0)), .atom (.add (.n 65) (.n 7) (.n 64)),
    .ite (.n 65) [] [.atom (.mul (.n 66) (.n 48) (.n 10)), .atom (.mul (.n 67) (.n 46) (.n 10)),
      .call "gkr_rounds__L1" [.n 66, .n 67, .n 4] [.n 68]]]

/-- The last record. -/
def lyR3 : List Stmt :=
  [.atom (.mul (.n 69) (.n 48) (.n 11))] ++
  (List.range 6).map (fun k ↦ .atom (.load (.n (70 + k)) (.n 69) (862 * k)))

/-- The children, four at a permutation. -/
def lyR4 : List Stmt :=
  ((List.range 4).map lyEvT).flatten ++
  [keccakA (lyRate 0 ++ (List.range 5).map fun k ↦ .n (70 + k)) (lyOuts 92)] ++
  ((List.range 4).map fun i ↦ lyEvT (4 + i)).flatten ++
  [keccakA (lyRate 1 ++ lyCap 92) (lyOuts 121)] ++
  ((List.range 4).map fun i ↦ lyEvT (8 + i)).flatten

/-- The last claim's check and the new coordinates. -/
def lyR5 : List Stmt :=
  [.atom (.load (.n 150) (.n 69) 5172),
    .atom (.mul (.n 151) (.n 137) (.n 141)), .atom (.mul (.n 152) (.n 151) (.n 145)),
    .atom (.mul (.n 153) (.n 152) (.n 149)), .atom (.const (.n 154) (word 0 0)),
    .atom (.mul (.n 155) (.n 42) (.n 154)), .atom (.add (.n 156) (.n 153) (.n 155)),
    .atom (.mul (.n 157) (.n 108) (.n 112)), .atom (.mul (.n 158) (.n 157) (.n 116)),
    .atom (.mul (.n 159) (.n 158) (.n 120)), .atom (.mul (.n 160) (.n 42) (.n 156)),
    .atom (.add (.n 161) (.n 159) (.n 160)), .atom (.mul (.n 162) (.n 79) (.n 83)),
    .atom (.mul (.n 163) (.n 162) (.n 87)), .atom (.mul (.n 164) (.n 163) (.n 91)),
    .atom (.mul (.n 165) (.n 42) (.n 161)), .atom (.add (.n 166) (.n 164) (.n 165)),
    .atom (.assertEq (.n 150) (.n 166)),
    keccakA (lyRate 2 ++ lyCap 121) (lyOuts 167)] ++
  challengeT (.n 167) 180 ++
  [keccakA ([.n 25, .n 25, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28] ++ lyCap 167) (lyOuts 181)] ++
  challengeT (.n 181) 194

/-- The next slot and the next iteration. -/
def lyR6 : List Stmt :=
  [.atom (.load (.n 180) (.n 46) 40), .atom (.load (.n 194) (.n 46) 41)] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (189 + k)) (.n 17) (26 + k))) ++
  [.atom (.const (.n 195) (word 4096 0)), .atom (.mul (.n 196) (.n 75) (.n 195)),
    .atom (.load (.n 196) (.n 17) 31)] ++
  lyValT 0 197 32 ++ lyValT 1 206 33 ++ lyValT 2 215 34 ++
  [.atom (.const (.n 224) (word 1099511627776 0)), .atom (.mul (.n 225) (.n 46) (.n 224)),
    .atom (.load (.n 225) (.n 17) 35), .atom (.mul (.n 226) (.n 47) (.n 11)),
    .atom (.const (.n 227) (word 2 0)), .atom (.mul (.n 228) (.n 226) (.n 227)),
    .atom (.load (.n 228) (.n 17) 36), .atom (.mul (.n 229) (.n 9) (.n 54)),
    .atom (.load (.n 230) (.n 229) 4), .atom (.mul (.n 231) (.n 53) (.n 230)),
    .atom (.load (.n 231) (.n 17) 37), .atom (.mul (.n 232) (.n 9) (.n 54)),
    .atom (.load (.n 233) (.n 232) 0), .atom (.load (.n 233) (.n 17) 38),
    .atom (.const (.n 234) (word 2 0)), .atom (.mul (.n 235) (.n 0) (.n 234)),
    .atom (.add (.n 236) (.n 235) (.n 1)), .atom (.const (.n 237) (word 2 0)),
    .atom (.mul (.n 238) (.n 0) (.n 237)),
    .callIf (.n 236) name% «verify_bus_gkr_loop0» [.n 238, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6,
        .n 7, .n 8, .n 9]]

set_option maxRecDepth 10000 in
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
    (hg : Good rd S w σ (.keccak ins (lyOuts b) false false)) :
    (Atom.keccak ins (lyOuts b) false false).Holds rd σ ∧
      (∀ k (hk : k < 13), σ (.n (b + k)) = cellsOfState (permOf (ins.map σ)) false ⟨k, hk⟩) ∧
      (lyCap b).map σ = capOf (permOf (ins.map σ)) := by
  obtain ⟨hk, -⟩ := keccak_good hg
  obtain ⟨hP, hc⟩ := ly_keccak hk
  exact ⟨hk, hP, hc⟩

/-- **The head**: the slot's pointer `layers·g^(13 L)`, the combiner's permutation over the
slot's capacity, the first record stored (its capacity, cursor and combined claim), `half` and
`parity`. -/
theorem lyc_head (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {j sh : ℕ}
    (hx : σ (.n 0) = gen ^ j) (hsg : σ (.n 2) = gen ^ (2 - sh)) (hsh : sh < 2) {s : Fs}
    {cur : E} {st : GkrState} {row pos half parity : E}
    (hS : GkSlot rd (σ (.n 3)) (2 * j + 2 - sh) s cur st row pos half parity)
    (hc0 : TbCapAt rd (σ (.n 5) * pos) 0 gkCap s.squeeze.2.cap)
    (hu0 : LoadHolds rd (σ (.n 5) * pos) (5 * gkCap) cur)
    (hl0 : LoadHolds rd (σ (.n 5) * pos) (6 * gkCap) (polyEval st.values s.squeeze.1)) :
    Stmt.HoldsList C rd σ lyR1 True kret ∧ σ (.n 10) = gen ^ (2 * j) ∧
      σ (.n 11) = gen ^ (2 * j + 2 - sh) ∧
      σ (.n 17) = σ (.n 3) * gen ^ (13 * (2 * j + 2 - sh)) ∧
      σ (.n 42) = s.squeeze.1 ∧ σ (.n 46) = row ∧ σ (.n 47) = pos ∧
      σ (.n 48) = σ (.n 5) * pos ∧ σ (.n 53) = half ∧ σ (.n 54) = parity ∧
      σ (.n 56) = 1 + half ∧ σ (.n 57) = 1 ∧ σ (.n 25) = 0 ∧ σ (.n 26) = 0 ∧
      σ (.n 27) = 0 ∧ σ (.n 28) = 0 := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  obtain ⟨hcl, hcap, hpe, hcur, hvl, hval, hrow, -, -, hpos, hhalf, hpar⟩ := hS
  set L := 2 * j + 2 - sh with hL
  have m10 := good_mul (g 0 (.mul (.n 10) (.n 0) (.n 0)) (by decide +kernel)) (by omega) (by omega)
  have m11 := good_mul (g 1 (.mul (.n 11) (.n 10) (.n 2)) (by decide +kernel)) (by omega) (by omega)
  have m12 := good_mul (g 2 (.mul (.n 12) (.n 11) (.n 11)) (by decide +kernel)) (by omega)
    (by omega)
  have m13 := good_mul (g 3 (.mul (.n 13) (.n 12) (.n 11)) (by decide +kernel)) (by omega)
    (by omega)
  have m14 := good_mul (g 4 (.mul (.n 14) (.n 13) (.n 13)) (by decide +kernel)) (by omega)
    (by omega)
  have m15 := good_mul (g 5 (.mul (.n 15) (.n 14) (.n 14)) (by decide +kernel)) (by omega)
    (by omega)
  have m16 := good_mul (g 6 (.mul (.n 16) (.n 15) (.n 11)) (by decide +kernel)) (by omega)
    (by omega)
  have m17 := good_mul (g 7 (.mul (.n 17) (.n 3) (.n 16)) (by decide +kernel)) (by omega) (by omega)
  have e10 : σ (.n 10) = gen ^ (2 * j) := by rw [m10, hx, ← pow_add]; ring_nf
  have e11 : σ (.n 11) = gen ^ L := by
    rw [m11, e10, hsg, ← pow_add, show 2 * j + (2 - sh) = L by omega]
  have e17 : σ (.n 17) = σ (.n 3) * gen ^ (13 * L) := by
    rw [m17, m16, m15, m14, m13, m12, e11, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
      ← pow_add]
    ring_nf
  have ld : ∀ k w, LoadHolds rd (σ (.n 17)) k w ↔ LoadHolds rd (σ (.n 3)) (13 * L + k) w := by
    intro k w; rw [e17, tb_loadHolds_mul_gen_pow]
  -- the slot's capacity and cursor
  have gcap := good_slice hG 8 ((List.range 6).map fun k ↦
    Stmt.atom (.load (.n (18 + k)) (.n 17) k)) (by decide +kernel) (by decide +kernel)
  have kcap : ∀ k < 6, some (18 + k, 17, k) ∉ lyS.map loadKey := by decide +kernel
  have rcap : ∀ k < 5, σ (.n (18 + k)) = s.cap.getD k 0 ∧
      LoadHolds rd (σ (.n 17)) k (σ (.n (18 + k))) := fun k hk =>
    good_readS (gcap _ (List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩))
      (kcap k (by omega)) ((ld k _).mpr (hcap k hk))
  obtain ⟨e23, l23⟩ := good_readS (gcap _ (List.mem_map.mpr ⟨5, List.mem_range.mpr (by omega),
    rfl⟩)) (kcap 5 (by omega)) ((ld 5 _).mpr hcur)
  have c24 : σ (.n 24) = word 1 0 := g 14 (.const (.n 24) (word 1 0)) (by decide +kernel)
  have c25 : σ (.n 25) = word 0 0 := g 15 (.const (.n 25) (word 0 0)) (by decide +kernel)
  have c26 : σ (.n 26) = word 0 0 := g 16 (.const (.n 26) (word 0 0)) (by decide +kernel)
  have c27 : σ (.n 27) = word 0 0 := g 17 (.const (.n 27) (word 0 0)) (by decide +kernel)
  have c28 : σ (.n 28) = word 0 0 := g 18 (.const (.n 28) (word 0 0)) (by decide +kernel)
  rw [tb_word_zero] at c25 c26 c27 c28
  -- the combiner's permutation
  have hcapE : ((List.range 5).map fun k ↦ V.n (18 + k)).map σ = s.cap := by
    rw [tb_eq_map_getD hcl, List.map_map]
    exact List.map_congr_left fun k hk => (rcap k (List.mem_range.mp hk)).1
  have hins : (([.n 25, .n 25, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28] ++
      (List.range 5).map fun k ↦ V.n (18 + k)) : List V).map σ = rateOf s.pend ++ s.cap := by
    rw [ly_zero_rate c25 c26 c27 c28, hpe, hcapE]
  obtain ⟨k19, hP, -⟩ := lyc_keccak (g 19 (.keccak ([.n 25, .n 25, .n 25, .n 25, .n 25, .n 26,
    .n 27, .n 28] ++ (List.range 5).map fun k ↦ .n (18 + k)) (lyOuts 29) false false)
    (by decide +kernel))
  rw [hins] at hP
  have hco := challengeT_good (good_slice hG 20 (challengeT (.n 29) 42) (by decide +kernel)
    (by decide +kernel))
  have e42 : σ (.n 42) = s.squeeze.1 := challengeT_value hco (hP 0 (by omega))
  -- the values, the row, the position, the first record
  have gv := good_slice hG 21 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (43 + k)) (.n 17) (6 + k))) (by decide +kernel) (by decide +kernel)
  have kv : ∀ k < 5, some (43 + k, 17, 6 + k) ∉ lyS.map loadKey := by decide +kernel
  have rv : ∀ k < 5, ∀ w, LoadHolds rd (σ (.n 3)) (13 * L + (6 + k)) w →
      σ (.n (43 + k)) = w ∧ LoadHolds rd (σ (.n 17)) (6 + k) (σ (.n (43 + k))) := fun k hk w hw =>
    good_readS (gv _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)) (kv k hk)
      ((ld (6 + k) _).mpr hw)
  obtain ⟨e43, l43⟩ := rv 0 (by omega) _ (by rw [← Nat.add_assoc]; exact hval 0 (by omega))
  obtain ⟨e44, l44⟩ := rv 1 (by omega) _ (by rw [← Nat.add_assoc]; exact hval 1 (by omega))
  obtain ⟨e45, l45⟩ := rv 2 (by omega) _ (by rw [← Nat.add_assoc]; exact hval 2 (by omega))
  obtain ⟨e46, l46⟩ := rv 3 (by omega) _ hrow
  obtain ⟨e47, l47⟩ := rv 4 (by omega) _ hpos
  have m48 := good_mul (g 26 (.mul (.n 48) (.n 5) (.n 47)) (by decide +kernel)) (by omega)
    (by omega)
  rw [e47] at m48
  have s37 : ∀ k < 5, LoadHolds rd (σ (.n 48)) (862 * k) (σ (.n (37 + k))) := by
    intro k hk
    have := tbCapAt_getD hc0 hk
    rw [show 0 + k * gkCap = 862 * k by unfold gkCap; ring] at this
    rw [m48, show 37 + k = 29 + (8 + k) by omega, hP (8 + k) (by omega)]
    rwa [Fs.squeeze, capOf_getD _ hk] at this
  have s23 : LoadHolds rd (σ (.n 48)) 4310 (σ (.n 23)) := by rw [m48, e23]; exact hu0
  have m49 := good_mul (g 33 (.mul (.n 49) (.n 42) (.n 45)) (by decide +kernel)) (by omega)
    (by omega)
  have a50 : σ (.n 50) = σ (.n 44) + σ (.n 49) := g 34 (.add (.n 50) (.n 44) (.n 49))
    (by decide +kernel)
  have m51 := good_mul (g 35 (.mul (.n 51) (.n 42) (.n 50)) (by decide +kernel)) (by omega)
    (by omega)
  have a52 : σ (.n 52) = σ (.n 43) + σ (.n 51) := g 36 (.add (.n 52) (.n 43) (.n 51))
    (by decide +kernel)
  have e52 : σ (.n 52) = polyEval st.values s.squeeze.1 := by
    obtain ⟨v0, v1, v2, hv3⟩ : ∃ v0 v1 v2, st.values = [v0, v1, v2] := by
      match st.values, hvl with
      | [v0, v1, v2], _ => exact ⟨v0, v1, v2, rfl⟩
    rw [a52, m51, a50, m49, e43, e44, e45, e42, hv3]
    simp only [polyEval, List.foldr, List.getD_cons_zero, List.getD_cons_succ]
    ring
  have s52 : LoadHolds rd (σ (.n 48)) 5172 (σ (.n 52)) := by rw [m48, e52]; exact hl0
  obtain ⟨e53, l53⟩ := good_read (g 38 (.load (.n 53) (.n 17) 11) (by decide +kernel))
    (by decide +kernel) ((ld 11 _).mpr hhalf)
  obtain ⟨e54, l54⟩ := good_read (g 39 (.load (.n 54) (.n 17) 12) (by decide +kernel))
    (by decide +kernel) ((ld 12 _).mpr hpar)
  have c55 : σ (.n 55) = word 1 0 := g 40 (.const (.n 55) (word 1 0)) (by decide +kernel)
  have a56 : σ (.n 56) = σ (.n 55) + σ (.n 53) := g 41 (.add (.n 56) (.n 55) (.n 53))
    (by decide +kernel)
  have c57 : σ (.n 57) = word 1 0 := g 42 (.const (.n 57) (word 1 0)) (by decide +kernel)
  rw [tb_word_one] at c24 c55 c57
  refine ⟨?_, e10, e11, e17, e42, e46, e47, m48, e53, e54, by rw [a56, c55, e53], c57, c25, c26,
    c27, c28⟩
  -- the region holds
  refine holdsList_straightN _ (by decide +kernel) ?_ trivial
  simp only [lyR1, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
    List.mem_range, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, and_assoc,
    keccakA, challengeT]
  refine ⟨m10, m11, m12, m13, m14, m15, m16, m17, fun k hk => ?_,
    show σ (.n 24) = word 1 0 by rw [c24, tb_word_one],
    show σ (.n 25) = word 0 0 by rw [c25, tb_word_zero],
    show σ (.n 26) = word 0 0 by rw [c26, tb_word_zero],
    show σ (.n 27) = word 0 0 by rw [c27, tb_word_zero],
    show σ (.n 28) = word 0 0 by rw [c28, tb_word_zero], k19, hco, fun k hk => ?_,
    show σ (.n 48) = σ (.n 5) * σ (.n 47) by rw [m48, e47], fun k hk => s37 k hk,
    s23, m49, a50, m51, a52, s52, l53, l54, show σ (.n 55) = word 1 0 by rw [c55, tb_word_one],
    a56, show σ (.n 57) = word 1 0 by rw [c57, tb_word_one]⟩
  · rcases Nat.lt_or_ge k 5 with h5 | h5
    · exact (rcap k h5).2
    · rw [show k = 5 by omega]; exact l23
  · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl
    · exact l43
    · exact l44
    · exact l45
    · exact l46
    · exact l47

theorem tb_isInK_one : IsInK (1 : E) := by simpa using tb_gen_pow_isInK 0

/-- **The rounds**: `verify_bus_gkr_loop0_loop0` (`8·(k/4)` rounds), `gkr_rounds__L{2r}` at `r = k %
4` (the dispatch on `parity = g^r`), and `gkr_rounds__L1` at an odd depth, each from its record,
when the
records hold every run of consecutive rounds. -/
theorem lyc_rounds (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {j k sh : ℕ}
    (hj : j < 2 ^ 30) (hsh2 : sh < 2) (hk : k = j + 1 - sh)
    (e10 : σ (.n 10) = gen ^ (2 * j)) (e7 : σ (.n 7) = gen ^ sh)
    (e53 : σ (.n 53) = gen ^ (k / 4)) (e54 : σ (.n 54) = gen ^ (k % 4))
    (e56 : σ (.n 56) = 1 + gen ^ (k / 4)) (e57 : σ (.n 57) = 1)
    (hT : ∀ a k', a + k' ≤ 2 * k + sh →
      TbGkrRoundsOut k' rd (σ (.n 48) * gen ^ a) (σ (.n 46) * gen ^ a)) :
    Stmt.HoldsList (coreProgram.Rel rd) rd σ lyR2 True kret := by
  have m58 := good_mul (ly_good hG 44 (.mul (.n 58) (.n 53) (.n 53)) (by decide +kernel))
    (by omega) (by omega)
  have m59 := good_mul (ly_good hG 45 (.mul (.n 59) (.n 58) (.n 58)) (by decide +kernel))
    (by omega) (by omega)
  have m60 := good_mul (ly_good hG 46 (.mul (.n 60) (.n 59) (.n 59)) (by decide +kernel))
    (by omega) (by omega)
  have m61 := good_mul (ly_good hG 47 (.mul (.n 61) (.n 48) (.n 60)) (by decide +kernel))
    (by omega) (by omega)
  have m62 := good_mul (ly_good hG 48 (.mul (.n 62) (.n 46) (.n 60)) (by decide +kernel))
    (by omega) (by omega)
  have e60 : σ (.n 60) = gen ^ (8 * (k / 4)) := by
    rw [m60, m59, m58, e53, ← pow_add, ← pow_add, ← pow_add]; ring_nf
  have c64 : σ (.n 64) = word 1 0 := ly_good hG 50 (.const (.n 64) (word 1 0)) (by decide +kernel)
  have a65 : σ (.n 65) = σ (.n 7) + σ (.n 64) :=
    ly_good hG 51 (.add (.n 65) (.n 7) (.n 64)) (by decide +kernel)
  rw [tb_word_one] at c64
  refine holdsList_of_vsh lyR2 (by decide +kernel) (fun s hs => ?_) trivial
  simp only [lyR2, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- `verify_bus_gkr_loop0_loop0`
    refine ⟨by rw [e56]; exact tb_isInK_add tb_isInK_one (tb_gen_pow_isInK _), fun hne => ?_⟩
    have hpos : 0 < k / 4 := by
      rcases Nat.eq_zero_or_pos (k / 4) with h0 | h0
      · rw [e56, h0, pow_zero, e_add_self] at hne; exact absurd rfl hne
      · exact h0
    simp only [List.map_cons, List.map_nil, e57, e53]
    exact l29_complete hpos (by omega) fun i hi => hT (8 * i) 8 (by omega)
  · exact m58
  · exact m59
  · exact m60
  · exact m61
  · exact m62
  · -- `gkr_rounds__L{2r}`, `r = k % 4`
    have gd := good_slice hG 49 [.dispatch (.n 54)
      ["gkr_rounds__L0", "gkr_rounds__L2", "gkr_rounds__L4", "gkr_rounds__L6"] [.n 61, .n 62, .n 4]
      [.n 63]] (by decide +kernel) rfl _ List.mem_cons_self
    have e63 : σ (.n 63) = 0 := gd (.n 63) List.mem_cons_self
    have hr : k % 4 < 4 := Nat.mod_lt _ (by omega)
    refine ⟨k % 4, by simpa using hr, by rw [e54, gen_pow_eq_ofK], ?_⟩
    simp only [List.map_cons, List.map_nil, e63]
    rw [m61, m62, e60]
    have hR := hT (8 * (k / 4)) (2 * (k % 4)) (by omega)
    have hr4 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    rcases hr4 with h | h | h | h <;> simp only [h, List.getElem_cons_zero,
      List.getElem_cons_succ] <;> rw [h] at hR
    · exact (gkr_rounds_holds.2 rd _ _).mpr rfl
    · exact (gkr_rounds_holds.1 2 (by simp [gkrRoundsCounts]) rd _ _).mpr ⟨rfl, hR⟩
    · exact (gkr_rounds_holds.1 4 (by simp [gkrRoundsCounts]) rd _ _).mpr ⟨rfl, hR⟩
    · exact (gkr_rounds_holds.1 6 (by simp [gkrRoundsCounts]) rd _ _).mpr ⟨rfl, hR⟩
  · exact c64.trans tb_word_one.symm
  · exact a65
  · -- `gkr_rounds__L1` at an odd depth
    have gb := good_ite hG 52 (.n 65) [] [.atom (.mul (.n 66) (.n 48) (.n 10)),
      .atom (.mul (.n 67) (.n 46) (.n 10)), .call "gkr_rounds__L1" [.n 66, .n 67, .n 4] [.n 68]]
      (by decide +kernel)
    refine ⟨by rw [a65, c64, e7]; exact tb_isInK_add (tb_gen_pow_isInK _) tb_isInK_one,
      fun _ s hs => absurd hs (by simp), fun hne s hs => ?_⟩
    have hsh1 : sh = 1 := by
      by_contra h
      rw [a65, c64, e7, show sh = 0 by omega, pow_zero, e_add_self] at hne
      exact hne rfl
    have m66 := good_mulS (gb (.atom (.mul (.n 66) (.n 48) (.n 10))) (by simp)) (by omega)
      (by omega)
    have m67 := good_mulS (gb (.atom (.mul (.n 67) (.n 46) (.n 10))) (by simp)) (by omega)
      (by omega)
    have e68 : σ (.n 68) = 0 :=
      gb (.call "gkr_rounds__L1" [.n 66, .n 67, .n 4] [.n 68]) (by simp) (.n 68) List.mem_cons_self
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact m66
    · exact m67
    · show coreProgram.Rel rd "gkr_rounds__L1" [σ (.n 66), σ (.n 67), σ (.n 4)] [σ (.n 68)]
      rw [m66, m67, e10, e68]
      exact (gkr_rounds_holds.1 1 (by simp [gkrRoundsCounts]) rd _ _).mpr
        ⟨rfl, hT (2 * j) 1 (by omega)⟩

/-- **The last record**: its capacity and cursor, at `rec·g^L`. -/
theorem lyc_last (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {L : ℕ}
    (e11 : σ (.n 11) = gen ^ L) {cap : List E} {cur : E}
    (hc : TbCapAt rd (σ (.n 48) * gen ^ L) 0 gkCap cap)
    (hu : LoadHolds rd (σ (.n 48) * gen ^ L) (5 * gkCap) cur) :
    Stmt.HoldsList C rd σ lyR3 True kret ∧ σ (.n 69) = σ (.n 48) * gen ^ L ∧
      (∀ k < 5, σ (.n (70 + k)) = cap.getD k 0) ∧ σ (.n 75) = cur := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  have m69 := good_mul (g 53 (.mul (.n 69) (.n 48) (.n 11)) (by decide +kernel)) (by omega)
    (by omega)
  rw [e11] at m69
  have gc := good_slice hG 54 ((List.range 6).map fun k ↦
    Stmt.atom (.load (.n (70 + k)) (.n 69) (862 * k))) (by decide +kernel) (by decide +kernel)
  have kc : ∀ k < 6, some (70 + k, 69, 862 * k) ∉ lyS.map loadKey := by decide +kernel
  have rc : ∀ k < 5, σ (.n (70 + k)) = cap.getD k 0 ∧
      LoadHolds rd (σ (.n 69)) (862 * k) (σ (.n (70 + k))) := fun k hk =>
    good_readS (gc _ (List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩)) (kc k (by omega))
      (by have := tbCapAt_getD hc hk
          rwa [m69, show 862 * k = 0 + k * gkCap by unfold gkCap; ring])
  obtain ⟨e75, l75⟩ := good_readS (gc _ (List.mem_map.mpr ⟨5, List.mem_range.mpr (by omega),
    rfl⟩)) (kc 5 (by omega)) (by rw [m69]; exact hu)
  refine ⟨?_, m69, fun k hk => (rc k hk).1, e75⟩
  refine holdsList_straightN _ (by decide +kernel) ?_ trivial
  simp only [lyR3, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
    List.mem_range, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨by show σ (.n 69) = σ (.n 48) * σ (.n 11); rw [m69, e11], fun k hk => ?_⟩
  rcases Nat.lt_or_ge k 5 with h5 | h5
  · exact (rc k h5).2
  · rw [show k = 5 by omega]; exact l75

/-- **The children**: the twelve words at the last record's cursor, read, and absorbed four at a
time over the last record's capacity. -/
theorem lyc_children (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {cap : List E}
    (hcl : cap.length = 5) (e70 : ∀ k < 5, σ (.n (70 + k)) = cap.getD k 0) {ch : List E}
    (hch : ch.length = 12) (hr : TbReadsAt rd (σ (.n 75)) ch) :
    Stmt.HoldsList C rd σ lyR4 True kret ∧
      (∀ i < 12, σ (.n (lyEv i)) = ch.getD i 0 ∧ σ (.n (lyEv i + 3)) = σ (.n (lyEv i)) ∧
        FsPackOk σ (.n (lyEv i)) (lyEv i + 1) dsObserve) ∧
      (lyCap 121).map σ = capOf (Fs.perm ⟨capOf (Fs.perm ⟨cap, (lyCh σ 0).map (·, dsObserve)⟩),
        (lyCh σ 1).map (·, dsObserve)⟩) := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  have hni : ∀ i < 12, (lyEvT i).all notIteB = true := by decide +kernel
  have hk : ∀ i < 12, some (lyEv i, 75, i) ∉ lyS.map loadKey := by decide +kernel
  have EV : ∀ i < 12, (∀ s ∈ lyEvT i, SHolds C rd σ s) ∧
      σ (.n (lyEv i)) = ch.getD i 0 ∧ σ (.n (lyEv i + 3)) = σ (.n (lyEv i)) ∧
      FsPackOk σ (.n (lyEv i)) (lyEv i + 1) dsObserve := by
    intro i hi
    have gb := good_slice hG (lyPos i) (lyEvT i) (lyEvs_check i hi) (hni i hi)
    have hl : LoadHolds rd (σ (.n 75)) (0 + i) (ch.getD i 0) := by
      have := hr i (by rw [hch]; exact hi)
      rw [← List.getD_eq_getElem _ 0] at this
      rwa [Nat.zero_add]
    obtain ⟨e0, -, hfs⟩ := fsNextT_good (C := C) (kret := kret)
      (fun s hs => gb s (by unfold lyEvT chT; exact List.mem_append_left _ hs))
      (by rw [Nat.zero_add]; exact hk i hi) hl
    have cp : σ (.n (lyEv i + 3)) = σ (.n (lyEv i)) :=
      gb (.atom (.copy (.n (lyEv i + 3)) (.n (lyEv i)))) (by simp [lyEvT, chT])
    obtain ⟨⟨hld, hok⟩, -⟩ := (holds_fsNextT _ _ _ _ _).mp hfs
    refine ⟨?_, e0, cp, hok⟩
    simp only [lyEvT, chT, fsNextT, fsPackT, List.forall_mem_append, List.forall_mem_cons,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, and_assoc]
    exact ⟨hld, hok.1, hok.2, cp⟩
  have hp : ∀ m < 3, ∀ i < 4,
      FsPackOk σ (.n (lyEv (4 * m + i))) (lyEv (4 * m + i) + 1) dsObserve :=
    fun m hm i hi => (EV (4 * m + i) (by omega)).2.2.2
  -- the first four children's permutation
  have hS0 : ((List.range 5).map fun k ↦ V.n (70 + k)).map σ = cap := by
    rw [tb_eq_map_getD hcl, List.map_map]
    apply List.map_congr_left
    intro k hk'
    exact e70 k (List.mem_range.mp hk')
  obtain ⟨k76, -⟩ := keccak_good (g 76 (.keccak (lyRate 0 ++ (List.range 5).map fun k ↦
    .n (70 + k)) (lyOuts 92) false false) (by decide +kernel))
  obtain ⟨-, B0⟩ := ly_perm_block (hp 0 (by omega)) k76
  rw [hS0] at B0
  obtain ⟨k93, -⟩ := keccak_good (g 93 (.keccak (lyRate 1 ++ lyCap 92) (lyOuts 121) false false)
    (by decide +kernel))
  obtain ⟨-, B1⟩ := ly_perm_block (hp 1 (by omega)) k93
  rw [B0] at B1
  refine ⟨?_, fun i hi => (EV i hi).2, B1⟩
  refine holdsList_straightN _ (by decide +kernel) ?_ trivial
  simp only [lyR4, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, and_true, and_assoc, keccakA]
  exact ⟨forall_flatten_range fun i hi => (EV i (by omega)).1, k76,
    forall_flatten_range fun i hi => (EV (4 + i) (by omega)).1, k93,
    forall_flatten_range fun i hi => (EV (8 + i) (by omega)).1⟩

/-- **The check and the two new coordinates**: the last claim, read at the last record, is the
children's products' polynomial at the combiner; the sponge after the twelve children squeezes the
two coordinates and leaves the capacity at `189 ..`. -/
theorem lyc_check (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {P1 : KeccakState}
    (cp : ∀ i < 12, σ (.n (lyEv i + 3)) = σ (.n (lyEv i)))
    (hpk : ∀ i < 12, FsPackOk σ (.n (lyEv i)) (lyEv i + 1) dsObserve)
    (hB1 : (lyCap 121).map σ = capOf P1) {claim : E}
    (hcl : LoadHolds rd (σ (.n 69)) 5172 claim)
    (hcheck : claim =
      polyEval [prodE (lyCh σ 0), prodE (lyCh σ 1), prodE (lyCh σ 2)] (σ (.n 42)))
    (c25 : σ (.n 25) = 0) (c26 : σ (.n 26) = 0) (c27 : σ (.n 27) = 0) (c28 : σ (.n 28) = 0) :
    Stmt.HoldsList C rd σ lyR5 True kret ∧
      σ (.n 180) = challengeOf (Fs.perm ⟨capOf P1, (lyCh σ 2).map (·, dsObserve)⟩) ∧
      σ (.n 194) = challengeOf (permOf (rateOf [] ++
        capOf (Fs.perm ⟨capOf P1, (lyCh σ 2).map (·, dsObserve)⟩))) ∧
      ((List.range 5).map fun k ↦ σ (.n (189 + k))) = capOf (permOf (rateOf [] ++
        capOf (Fs.perm ⟨capOf P1, (lyCh σ 2).map (·, dsObserve)⟩))) := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  obtain ⟨e150, l150⟩ := good_read (g 110 (.load (.n 150) (.n 69) 5172) (by decide +kernel))
    (by decide +kernel) hcl
  -- the check
  have m151 := good_mul (g 111 (.mul (.n 151) (.n 137) (.n 141)) (by decide +kernel)) (by omega)
    (by omega)
  have m152 := good_mul (g 112 (.mul (.n 152) (.n 151) (.n 145)) (by decide +kernel)) (by omega)
    (by omega)
  have m153 := good_mul (g 113 (.mul (.n 153) (.n 152) (.n 149)) (by decide +kernel)) (by omega)
    (by omega)
  have c154 : σ (.n 154) = word 0 0 := g 114 (.const (.n 154) (word 0 0)) (by decide +kernel)
  have m155 := good_mul (g 115 (.mul (.n 155) (.n 42) (.n 154)) (by decide +kernel)) (by omega)
    (by omega)
  have a156 : σ (.n 156) = σ (.n 153) + σ (.n 155) :=
    g 116 (.add (.n 156) (.n 153) (.n 155)) (by decide +kernel)
  have m157 := good_mul (g 117 (.mul (.n 157) (.n 108) (.n 112)) (by decide +kernel)) (by omega)
    (by omega)
  have m158 := good_mul (g 118 (.mul (.n 158) (.n 157) (.n 116)) (by decide +kernel)) (by omega)
    (by omega)
  have m159 := good_mul (g 119 (.mul (.n 159) (.n 158) (.n 120)) (by decide +kernel)) (by omega)
    (by omega)
  have m160 := good_mul (g 120 (.mul (.n 160) (.n 42) (.n 156)) (by decide +kernel)) (by omega)
    (by omega)
  have a161 : σ (.n 161) = σ (.n 159) + σ (.n 160) :=
    g 121 (.add (.n 161) (.n 159) (.n 160)) (by decide +kernel)
  have m162 := good_mul (g 122 (.mul (.n 162) (.n 79) (.n 83)) (by decide +kernel)) (by omega)
    (by omega)
  have m163 := good_mul (g 123 (.mul (.n 163) (.n 162) (.n 87)) (by decide +kernel)) (by omega)
    (by omega)
  have m164 := good_mul (g 124 (.mul (.n 164) (.n 163) (.n 91)) (by decide +kernel)) (by omega)
    (by omega)
  have m165 := good_mul (g 125 (.mul (.n 165) (.n 42) (.n 161)) (by decide +kernel)) (by omega)
    (by omega)
  have a166 : σ (.n 166) = σ (.n 164) + σ (.n 165) :=
    g 126 (.add (.n 166) (.n 164) (.n 165)) (by decide +kernel)
  have e166 : σ (.n 166) =
      polyEval [prodE (lyCh σ 0), prodE (lyCh σ 1), prodE (lyCh σ 2)] (σ (.n 42)) := by
    rw [a166, m165, a161, m160, a156, m155, c154, tb_word_zero, m153, m152, m151, m159, m158, m157,
      m164, m163, m162,
      show σ (.n 79) = σ (.n 76) from cp 0 (by omega), show σ (.n 83) = σ (.n 80) from cp 1 (by omega),
      show σ (.n 87) = σ (.n 84) from cp 2 (by omega),
      show σ (.n 91) = σ (.n 88) from cp 3 (by omega),
      show σ (.n 108) = σ (.n 105) from cp 4 (by omega),
      show σ (.n 112) = σ (.n 109) from cp 5 (by omega),
      show σ (.n 116) = σ (.n 113) from cp 6 (by omega),
      show σ (.n 120) = σ (.n 117) from cp 7 (by omega),
      show σ (.n 137) = σ (.n 134) from cp 8 (by omega),
      show σ (.n 141) = σ (.n 138) from cp 9 (by omega),
      show σ (.n 145) = σ (.n 142) from cp 10 (by omega),
      show σ (.n 149) = σ (.n 146) from cp 11 (by omega)]
    have hc0 : lyCh σ 0 = [σ (.n 76), σ (.n 80), σ (.n 84), σ (.n 88)] := by rw [lyCh_eq]; rfl
    have hc1 : lyCh σ 1 = [σ (.n 105), σ (.n 109), σ (.n 113), σ (.n 117)] := by rw [lyCh_eq]; rfl
    have hc2 : lyCh σ 2 = [σ (.n 134), σ (.n 138), σ (.n 142), σ (.n 146)] := by rw [lyCh_eq]; rfl
    rw [hc0, hc1, hc2]
    simp only [polyEval, prodE, List.foldr, List.foldl]
    ring
  -- the third block's permutation
  have hp2 : ∀ i < 4, FsPackOk σ (.n (lyEv (4 * 2 + i))) (lyEv (4 * 2 + i) + 1) dsObserve :=
    fun i hi => hpk (4 * 2 + i) (by omega)
  obtain ⟨k128, -⟩ := keccak_good (g 128 (.keccak (lyRate 2 ++ lyCap 121) (lyOuts 167) false false)
    (by decide +kernel))
  obtain ⟨P2, B2⟩ := ly_perm_block hp2 k128
  rw [hB1] at P2 B2
  set Q := Fs.perm ⟨capOf P1, (lyCh σ 2).map (·, dsObserve)⟩ with hQ
  -- the first coordinate
  have hco2 := challengeT_good (good_slice hG 129 (challengeT (.n 167) 180)
    (by decide +kernel) (by decide +kernel))
  have e180 : σ (.n 180) = challengeOf Q := challengeT_value hco2 (P2 0 (by omega))
  -- the second
  have hz : (([.n 25, .n 25, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28] ++ lyCap 167 : List V).map σ) =
      rateOf [] ++ capOf Q := by
    rw [ly_zero_rate c25 c26 c27 c28, B2]
  obtain ⟨k130, P3, B3⟩ := lyc_keccak (g 130 (.keccak ([.n 25, .n 25, .n 25, .n 25, .n 25, .n 26,
    .n 27, .n 28] ++ lyCap 167) (lyOuts 181) false false) (by decide +kernel))
  rw [hz] at P3 B3
  have hco3 := challengeT_good (good_slice hG 131 (challengeT (.n 181) 194)
    (by decide +kernel) (by decide +kernel))
  have e194 : σ (.n 194) = challengeOf (permOf (rateOf [] ++ capOf Q)) :=
    challengeT_value hco3 (P3 0 (by omega))
  refine ⟨?_, e180, e194, ?_⟩
  · refine holdsList_straightN _ (by decide +kernel) ?_ trivial
    simp only [lyR5, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true, and_assoc, keccakA, challengeT]
    exact ⟨l150, m151, m152, m153, c154, m155, a156, m157, m158, m159, m160, a161, m162, m163,
      m164, m165, a166, show σ (.n 150) + σ (.n 166) = 0 by rw [e150, hcheck, ← e166, e_add_self],
      k128, hco2, k130, hco3⟩
  · rw [← B3]
    simp [lyCap]

/-- A tree's new value on its equations: its four children's multilinear value at the two new
coordinates, stored at `off`. -/
theorem lyc_val (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {t b off : ℕ} (n : ℕ)
    (heq : tbStmtsEqb (lyValT t b off) ((lyPre.drop n).take (lyValT t b off).length) = true)
    (ht : t < 3) (hb : 194 < b)
    (hl : LoadHolds rd (σ (.n 17)) off (multilinearEval (lyCh σ t) [σ (.n 180), σ (.n 194)]))
    (cp : ∀ i < 12, σ (.n (lyEv i + 3)) = σ (.n (lyEv i))) :
    ∀ s ∈ lyValT t b off, SHolds C rd σ s := by
  have gb := good_slice hG n (lyValT t b off) heq (by simp [lyValT, chValT, notIteB])
  have he : ∀ i < 4, lyEv (4 * t + i) + 3 < b := by
    intro i hi; unfold lyEv chB; omega
  have a0 : σ (.n b) = σ (.n (lyEv (4 * t + 0) + 3)) + σ (.n (lyEv (4 * t + 1) + 3)) :=
    gb (.atom (.add (.n b) _ _)) (by simp [lyValT, chValT])
  have m1 := good_mulS (gb (.atom (.mul (.n (b + 1)) (.n 180) (.n b))) (by simp [lyValT, chValT]))
    (by omega) (by omega)
  have a2 : σ (.n (b + 2)) = σ (.n (lyEv (4 * t + 0) + 3)) + σ (.n (b + 1)) :=
    gb (.atom (.add (.n (b + 2)) _ _)) (by simp [lyValT, chValT])
  have a3 : σ (.n (b + 3)) = σ (.n (lyEv (4 * t + 2) + 3)) + σ (.n (lyEv (4 * t + 3) + 3)) :=
    gb (.atom (.add (.n (b + 3)) _ _)) (by simp [lyValT, chValT])
  have m4 := good_mulS (gb (.atom (.mul (.n (b + 4)) (.n 180) (.n (b + 3))))
    (by simp [lyValT, chValT])) (by omega) (by omega)
  have a5 : σ (.n (b + 5)) = σ (.n (lyEv (4 * t + 2) + 3)) + σ (.n (b + 4)) :=
    gb (.atom (.add (.n (b + 5)) _ _)) (by simp [lyValT, chValT])
  have a6 : σ (.n (b + 6)) = σ (.n (b + 2)) + σ (.n (b + 5)) :=
    gb (.atom (.add (.n (b + 6)) _ _)) (by simp [lyValT, chValT])
  have m7 := good_mulS (gb (.atom (.mul (.n (b + 7)) (.n 194) (.n (b + 6))))
    (by simp [lyValT, chValT])) (by omega) (by omega)
  have a8 : σ (.n (b + 8)) = σ (.n (b + 2)) + σ (.n (b + 7)) :=
    gb (.atom (.add (.n (b + 8)) _ _)) (by simp [lyValT, chValT])
  have e8 : σ (.n (b + 8)) = multilinearEval (lyCh σ t) [σ (.n 180), σ (.n 194)] := by
    rw [a8, m7, a6, a5, m4, a3, a2, m1, a0, cp (4 * t + 0) (by omega), cp (4 * t + 1) (by omega),
      cp (4 * t + 2) (by omega), cp (4 * t + 3) (by omega), lyCh_eq]
    simp only [multilinearEval, List.foldl, foldPairs, List.headD]
    ring_nf
  simp only [lyValT, chValT, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  exact ⟨a0, m1, a2, a3, m4, a5, a6, m7, a8, show LoadHolds rd (σ (.n 17)) off (σ (.n (b + 8))) by
    rw [e8]; exact hl⟩

/-- **The next slot and the next iteration**: the stores of the slot `26` words on, and the call
at `x·g` below the bound. -/
theorem lyc_stores (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s)
    (cp : ∀ i < 12, σ (.n (lyEv i + 3)) = σ (.n (lyEv i)))
    (s40 : LoadHolds rd (σ (.n 46)) 40 (σ (.n 180)))
    (s41 : LoadHolds rd (σ (.n 46)) 41 (σ (.n 194)))
    (s26 : ∀ k < 5, LoadHolds rd (σ (.n 17)) (26 + k) (σ (.n (189 + k))))
    (s31 : LoadHolds rd (σ (.n 17)) 31 (σ (.n 75) * gen ^ 12))
    (sv : ∀ t < 3, LoadHolds rd (σ (.n 17)) (32 + t)
      (multilinearEval (lyCh σ t) [σ (.n 180), σ (.n 194)]))
    (s35 : LoadHolds rd (σ (.n 17)) 35 (σ (.n 46) * gen ^ 40))
    (s36 : LoadHolds rd (σ (.n 17)) 36 (σ (.n 47) * σ (.n 11) * gen))
    {hv pv : E} (k4 : LoadHolds rd (σ (.n 9) * σ (.n 54)) 4 hv)
    (k0 : LoadHolds rd (σ (.n 9) * σ (.n 54)) 0 pv)
    (s37 : LoadHolds rd (σ (.n 17)) 37 (σ (.n 53) * hv))
    (s38 : LoadHolds rd (σ (.n 17)) 38 pv)
    (hK : IsInK (σ (.n 0) * gen + σ (.n 1)))
    (hcall : σ (.n 0) * gen + σ (.n 1) ≠ 0 →
      C name% «verify_bus_gkr_loop0» [σ (.n 0) * gen, σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4),
          σ (.n 5), σ (.n 6),
        σ (.n 7), σ (.n 8), σ (.n 9)] []) :
    Stmt.HoldsList C rd σ lyR6 True kret := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  have c195 : σ (.n 195) = word 4096 0 := g 139 (.const (.n 195) (word 4096 0))
    (by decide +kernel)
  have m196 := good_mul (g 140 (.mul (.n 196) (.n 75) (.n 195)) (by decide +kernel)) (by omega)
    (by omega)
  have c224 : σ (.n 224) = word 1099511627776 0 :=
    g 172 (.const (.n 224) (word 1099511627776 0)) (by decide +kernel)
  have m225 := good_mul (g 173 (.mul (.n 225) (.n 46) (.n 224)) (by decide +kernel)) (by omega)
    (by omega)
  have m226 := good_mul (g 175 (.mul (.n 226) (.n 47) (.n 11)) (by decide +kernel)) (by omega)
    (by omega)
  have c227 : σ (.n 227) = word 2 0 := g 176 (.const (.n 227) (word 2 0)) (by decide +kernel)
  have m228 := good_mul (g 177 (.mul (.n 228) (.n 226) (.n 227)) (by decide +kernel)) (by omega)
    (by omega)
  have m229 := good_mul (g 179 (.mul (.n 229) (.n 9) (.n 54)) (by decide +kernel)) (by omega)
    (by omega)
  obtain ⟨e230, l230⟩ := good_read (g 180 (.load (.n 230) (.n 229) 4) (by decide +kernel))
    (by decide +kernel) (by rw [m229]; exact k4)
  have m231 := good_mul (g 181 (.mul (.n 231) (.n 53) (.n 230)) (by decide +kernel)) (by omega)
    (by omega)
  have m232 := good_mul (g 183 (.mul (.n 232) (.n 9) (.n 54)) (by decide +kernel)) (by omega)
    (by omega)
  obtain ⟨e233, l233⟩ := good_read (g 184 (.load (.n 233) (.n 232) 0) (by decide +kernel))
    (by decide +kernel) (by rw [m232]; exact k0)
  have c234 : σ (.n 234) = word 2 0 := g 186 (.const (.n 234) (word 2 0)) (by decide +kernel)
  have m235 := good_mul (g 187 (.mul (.n 235) (.n 0) (.n 234)) (by decide +kernel)) (by omega)
    (by omega)
  have a236 : σ (.n 236) = σ (.n 235) + σ (.n 1) :=
    g 188 (.add (.n 236) (.n 235) (.n 1)) (by decide +kernel)
  have c237 : σ (.n 237) = word 2 0 := g 189 (.const (.n 237) (word 2 0)) (by decide +kernel)
  have m238 := good_mul (g 190 (.mul (.n 238) (.n 0) (.n 237)) (by decide +kernel)) (by omega)
    (by omega)
  have w4096 : word 4096 0 = gen ^ 12 := by
    rw [show (4096 : ℕ) = 2 ^ 12 by norm_num, tb_word_two_pow (by norm_num)]
  have w40 : word 1099511627776 0 = gen ^ 40 := by
    rw [show (1099511627776 : ℕ) = 2 ^ 40 by norm_num, tb_word_two_pow (by norm_num)]
  rw [tb_word_gen] at c227 c234 c237
  refine holdsList_straightN _ (by decide +kernel) ?_ trivial
  simp only [lyR6, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
    List.mem_range, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, and_assoc]
  refine ⟨s40, s41, fun k hk => s26 k hk, c195, m196,
    show LoadHolds rd (σ (.n 17)) 31 (σ (.n 196)) by rw [m196, c195, w4096]; exact s31,
    lyc_val hG 142 (by decide +kernel) (by omega) (by omega) (sv 0 (by omega)) cp,
    lyc_val hG 152 (by decide +kernel) (by omega) (by omega) (sv 1 (by omega)) cp,
    lyc_val hG 162 (by decide +kernel) (by omega) (by omega) (sv 2 (by omega)) cp,
    c224, m225, show LoadHolds rd (σ (.n 17)) 35 (σ (.n 225)) by rw [m225, c224, w40]; exact s35,
    m226, show σ (.n 227) = word 2 0 by rw [c227, tb_word_gen], m228,
    show LoadHolds rd (σ (.n 17)) 36 (σ (.n 228)) by rw [m228, m226, c227]; exact s36,
    m229, l230, m231, show LoadHolds rd (σ (.n 17)) 37 (σ (.n 231)) by rw [m231, e230]; exact s37,
    m232, l233, show LoadHolds rd (σ (.n 17)) 38 (σ (.n 233)) by rw [e233]; exact s38,
    show σ (.n 234) = word 2 0 by rw [c234, tb_word_gen], m235, a236,
    show σ (.n 237) = word 2 0 by rw [c237, tb_word_gen], m238,
    ⟨by rw [a236, m235, c234]; exact hK, fun hne => ?_⟩⟩
  show C name% «verify_bus_gkr_loop0» (List.map σ [.n 238, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6,
      .n 7, .n 8, .n 9]) []
  simp only [List.map_cons, List.map_nil]
  rw [m238, c237]
  exact hcall (by rw [a236, m235, c234] at hne; exact hne)

end Eval

end
end LeanVM.Guest.B1.Tables
