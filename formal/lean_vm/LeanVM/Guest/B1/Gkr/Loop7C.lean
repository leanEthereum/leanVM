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
# `verify_bus_gkr_loop0`, completely

An iteration at `x = g^j` from the slot of `L = 2j + 2 - sh` (`GkSlot`, the slot's words, nothing
waiting) runs one step of two levels (`GkStepD`, read back from the walk by `gkrStep_invT`). On a
memory holding the slot, the step's words at the cursor, the round records (`LyRecs`) and the
next slot, the body evaluated forward (`lyEvL`, its `ite`'s branches in order) holds region by
region (`lyR1 .. lyR6`):

* `lyc_head`: the combiner's permutation, the point row, the first record stored;
* `lyc_rounds`: `verify_bus_gkr_loop0_loop0`, then `gkr_rounds__L2`, or `gkr_rounds__L1` at an odd
  depth;
* `lyc_last`: the last record read;
* `lyc_children`: the twelve children read and absorbed, four at a permutation;
* `lyc_check`: the last claim read and checked, the two new coordinates;
* `lyc_stores`: the next slot and the next row's first cells stored, and the next iteration
  called.

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

theorem ly_chk : (chk 11 lyEvL).isSome = true := by decide +kernel

/-- `verify_bus_gkr_loop0`'s stores. -/
noncomputable def lyS : List Atom := storesOf 11 lyEvL

/-- The head: the slot's pointer, the combiner, the point row, the first record. -/
def lyR1 : List Stmt :=
  [.atom (.mul (.n 11) (.n 0) (.n 0)), .atom (.mul (.n 12) (.n 11) (.n 2)),
    .atom (.mul (.n 13) (.n 12) (.n 12)), .atom (.mul (.n 14) (.n 13) (.n 13)),
    .atom (.mul (.n 15) (.n 14) (.n 12)), .atom (.mul (.n 16) (.n 15) (.n 15)),
    .atom (.mul (.n 17) (.n 3) (.n 16))] ++
  (List.range 6).map (fun k ↦ .atom (.load (.n (18 + k)) (.n 17) k)) ++
  [.atom (.const (.n 24) (word 1 0)), .atom (.const (.n 25) (word 0 0)),
    .atom (.const (.n 26) (word 0 0)), .atom (.const (.n 27) (word 0 0)),
    .atom (.const (.n 28) (word 0 0)),
    keccakA ([.n 25, .n 25, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28] ++
      (List.range 5).map fun k ↦ .n (18 + k)) (lyOuts 29)] ++
  challengeT (.n 29) 42 ++
  (List.range 4).map (fun k ↦ .atom (.load (.n (43 + k)) (.n 17) (6 + k))) ++
  [.atom (.const (.n 47) (word 2 0)), .atom (.mul (.n 48) (.n 0) (.n 47)),
    .atom (.mul (.n 49) (.n 48) (.n 48)), .atom (.mul (.n 50) (.n 49) (.n 49)),
    .atom (.mul (.n 51) (.n 50) (.n 48)), .atom (.mul (.n 52) (.n 51) (.n 51)),
    .atom (.mul (.n 53) (.n 52) (.n 52)), .atom (.mul (.n 54) (.n 53) (.n 53)),
    .atom (.mul (.n 55) (.n 5) (.n 54)), .atom (.mul (.n 56) (.n 6) (.n 46))] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (37 + k)) (.n 56) (862 * k))) ++
  [.atom (.load (.n 23) (.n 56) 4310), .atom (.mul (.n 57) (.n 42) (.n 45)),
    .atom (.add (.n 58) (.n 44) (.n 57)), .atom (.mul (.n 59) (.n 42) (.n 58)),
    .atom (.add (.n 60) (.n 43) (.n 59)), .atom (.load (.n 60) (.n 56) 5172)]

/-- The rounds: `verify_bus_gkr_loop0_loop0`, the last record's cursor, the last rounds. -/
def lyR2 : List Stmt :=
  [.atom (.const (.n 61) (word 1 0)), .atom (.add (.n 62) (.n 61) (.n 0)),
    .atom (.const (.n 63) (word 1 0)),
    .callIf (.n 62) name% «verify_bus_gkr_loop0_loop0» [.n 63, .n 0, .n 56, .n 55, .n 4],
    .atom (.mul (.n 64) (.n 56) (.n 0)), .atom (.load (.n 65) (.n 64) 4310),
    .atom (.const (.n 66) (word 1 0)), .atom (.add (.n 67) (.n 8) (.n 66)),
    .ite (.n 67) ly72 ly71]

/-- The last record. -/
def lyR3 : List Stmt :=
  [.atom (.mul (.n 72) (.n 56) (.n 0)), .atom (.const (.n 73) (word 2 0)),
    .atom (.mul (.n 74) (.n 72) (.n 73))] ++
  (List.range 6).map (fun k ↦ .atom (.load (.n (75 + k)) (.n 74) (862 * k)))

/-- The children, four at a permutation. -/
def lyR4 : List Stmt :=
  ((List.range 4).map lyEvT).flatten ++
  [keccakA (lyRate 0 ++ (List.range 5).map fun k ↦ .n (75 + k)) (lyOuts 97)] ++
  ((List.range 4).map fun i ↦ lyEvT (4 + i)).flatten ++
  [keccakA (lyRate 1 ++ lyCap 97) (lyOuts 126)] ++
  ((List.range 4).map fun i ↦ lyEvT (8 + i)).flatten

/-- The last claim's check and the new coordinates. -/
def lyR5 : List Stmt :=
  [.atom (.load (.n 155) (.n 74) 5172),
    .atom (.mul (.n 156) (.n 142) (.n 146)), .atom (.mul (.n 157) (.n 156) (.n 150)),
    .atom (.mul (.n 158) (.n 157) (.n 154)), .atom (.const (.n 159) (word 0 0)),
    .atom (.mul (.n 160) (.n 42) (.n 159)), .atom (.add (.n 161) (.n 158) (.n 160)),
    .atom (.mul (.n 162) (.n 113) (.n 117)), .atom (.mul (.n 163) (.n 162) (.n 121)),
    .atom (.mul (.n 164) (.n 163) (.n 125)), .atom (.mul (.n 165) (.n 42) (.n 161)),
    .atom (.add (.n 166) (.n 164) (.n 165)), .atom (.mul (.n 167) (.n 84) (.n 88)),
    .atom (.mul (.n 168) (.n 167) (.n 92)), .atom (.mul (.n 169) (.n 168) (.n 96)),
    .atom (.mul (.n 170) (.n 42) (.n 166)), .atom (.add (.n 171) (.n 169) (.n 170)),
    .atom (.assertEq (.n 155) (.n 171)),
    keccakA (lyRate 2 ++ lyCap 126) (lyOuts 172)] ++
  challengeT (.n 172) 185 ++
  [keccakA ([.n 25, .n 25, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28] ++ lyCap 172) (lyOuts 186)] ++
  challengeT (.n 186) 199

/-- The next slot and the next iteration. -/
def lyR6 : List Stmt :=
  [.atom (.load (.n 185) (.n 55) 40), .atom (.load (.n 199) (.n 55) 41)] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (194 + k)) (.n 17) (20 + k))) ++
  [.atom (.const (.n 200) (word 4096 0)), .atom (.mul (.n 201) (.n 80) (.n 200)),
    .atom (.load (.n 201) (.n 17) 25)] ++
  lyValT 0 202 26 ++ lyValT 1 211 27 ++ lyValT 2 220 28 ++
  [.atom (.mul (.n 229) (.n 46) (.n 0)), .atom (.const (.n 230) (word 4 0)),
    .atom (.mul (.n 231) (.n 229) (.n 230)), .atom (.load (.n 231) (.n 17) 29),
    .atom (.const (.n 232) (word 2 0)), .atom (.mul (.n 233) (.n 0) (.n 232)),
    .atom (.add (.n 234) (.n 233) (.n 1)), .atom (.const (.n 235) (word 2 0)),
    .atom (.mul (.n 236) (.n 0) (.n 235)),
    .callIf (.n 234) name% «verify_bus_gkr_loop0» [.n 236, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6,
        .n 7, .n 8, .n 9, .n 10]]

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

/-- **The head**: the slot's pointer `layers·g^(10 L)`, the combiner's permutation over the
slot's capacity, the point row `pts·g^(40(j + 1))`, and the first record stored at `rounds·pos`
(its capacity, cursor and combined claim). -/
theorem lyc_head (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {j sh : ℕ}
    (hx : σ (.n 0) = gen ^ j) (hsg : σ (.n 2) = gen ^ (2 - sh)) (hsh : sh < 2) {s : Fs}
    {cur : E} {st : GkrState} {row pos : E}
    (hS : GkSlot rd (σ (.n 3)) (2 * j + 2 - sh) s cur st row pos)
    (hc0 : TbCapAt rd (σ (.n 6) * pos) 0 gkCap s.squeeze.2.cap)
    (hu0 : LoadHolds rd (σ (.n 6) * pos) (5 * gkCap) cur)
    (hl0 : LoadHolds rd (σ (.n 6) * pos) (6 * gkCap) (polyEval st.values s.squeeze.1)) :
    Stmt.HoldsList C rd σ lyR1 True kret ∧ σ (.n 11) = gen ^ (2 * j) ∧
      σ (.n 12) = gen ^ (2 * j + 2 - sh) ∧
      σ (.n 17) = σ (.n 3) * gen ^ (10 * (2 * j + 2 - sh)) ∧
      σ (.n 42) = s.squeeze.1 ∧ σ (.n 46) = pos ∧ σ (.n 55) = σ (.n 5) * gen ^ (40 * (j + 1)) ∧
      σ (.n 56) = σ (.n 6) * pos ∧ σ (.n 25) = 0 ∧ σ (.n 26) = 0 ∧
      σ (.n 27) = 0 ∧ σ (.n 28) = 0 := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  obtain ⟨hcl, hcap, hpe, hcur, hvl, hval, -, -, hpos⟩ := hS
  set L := 2 * j + 2 - sh with hL
  have m11 := good_mul (g 0 (.mul (.n 11) (.n 0) (.n 0)) (by decide +kernel)) (by omega) (by omega)
  have m12 := good_mul (g 1 (.mul (.n 12) (.n 11) (.n 2)) (by decide +kernel)) (by omega)
    (by omega)
  have m13 := good_mul (g 2 (.mul (.n 13) (.n 12) (.n 12)) (by decide +kernel)) (by omega)
    (by omega)
  have m14 := good_mul (g 3 (.mul (.n 14) (.n 13) (.n 13)) (by decide +kernel)) (by omega)
    (by omega)
  have m15 := good_mul (g 4 (.mul (.n 15) (.n 14) (.n 12)) (by decide +kernel)) (by omega)
    (by omega)
  have m16 := good_mul (g 5 (.mul (.n 16) (.n 15) (.n 15)) (by decide +kernel)) (by omega)
    (by omega)
  have m17 := good_mul (g 6 (.mul (.n 17) (.n 3) (.n 16)) (by decide +kernel)) (by omega) (by omega)
  have e11 : σ (.n 11) = gen ^ (2 * j) := by rw [m11, hx, ← pow_add]; ring_nf
  have e12 : σ (.n 12) = gen ^ L := by
    rw [m12, e11, hsg, ← pow_add, show 2 * j + (2 - sh) = L by omega]
  have e17 : σ (.n 17) = σ (.n 3) * gen ^ (10 * L) := by
    rw [m17, m16, m15, m14, m13, e12, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    ring_nf
  have ld : ∀ k w, LoadHolds rd (σ (.n 17)) k w ↔ LoadHolds rd (σ (.n 3)) (10 * L + k) w := by
    intro k w; rw [e17, tb_loadHolds_mul_gen_pow]
  -- the slot's capacity and cursor
  have gcap := good_slice hG 7 ((List.range 6).map fun k ↦
    Stmt.atom (.load (.n (18 + k)) (.n 17) k)) (by decide +kernel) (by decide +kernel)
  have kcap : ∀ k < 6, some (18 + k, 17, k) ∉ lyS.map loadKey := by decide +kernel
  have rcap : ∀ k < 5, σ (.n (18 + k)) = s.cap.getD k 0 ∧
      LoadHolds rd (σ (.n 17)) k (σ (.n (18 + k))) := fun k hk =>
    good_readS (gcap _ (List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩))
      (kcap k (by omega)) ((ld k _).mpr (hcap k hk))
  obtain ⟨e23, l23⟩ := good_readS (gcap _ (List.mem_map.mpr ⟨5, List.mem_range.mpr (by omega),
    rfl⟩)) (kcap 5 (by omega)) ((ld 5 _).mpr hcur)
  have c24 : σ (.n 24) = word 1 0 := g 13 (.const (.n 24) (word 1 0)) (by decide +kernel)
  have c25 : σ (.n 25) = word 0 0 := g 14 (.const (.n 25) (word 0 0)) (by decide +kernel)
  have c26 : σ (.n 26) = word 0 0 := g 15 (.const (.n 26) (word 0 0)) (by decide +kernel)
  have c27 : σ (.n 27) = word 0 0 := g 16 (.const (.n 27) (word 0 0)) (by decide +kernel)
  have c28 : σ (.n 28) = word 0 0 := g 17 (.const (.n 28) (word 0 0)) (by decide +kernel)
  rw [tb_word_zero] at c25 c26 c27 c28
  -- the combiner's permutation
  have hcapE : ((List.range 5).map fun k ↦ V.n (18 + k)).map σ = s.cap := by
    rw [tb_eq_map_getD hcl, List.map_map]
    exact List.map_congr_left fun k hk => (rcap k (List.mem_range.mp hk)).1
  have hins : (([.n 25, .n 25, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28] ++
      (List.range 5).map fun k ↦ V.n (18 + k)) : List V).map σ = rateOf s.pend ++ s.cap := by
    rw [ly_zero_rate c25 c26 c27 c28, hpe, hcapE]
  obtain ⟨k18, hP, -⟩ := lyc_keccak (g 18 (.keccak ([.n 25, .n 25, .n 25, .n 25, .n 25, .n 26,
    .n 27, .n 28] ++ (List.range 5).map fun k ↦ .n (18 + k)) (lyOuts 29) false false)
    (by decide +kernel))
  rw [hins] at hP
  have hco := challengeT_good (good_slice hG 19 (challengeT (.n 29) 42) (by decide +kernel)
    (by decide +kernel))
  have e42 : σ (.n 42) = s.squeeze.1 := challengeT_value hco (hP 0 (by omega))
  -- the values and the position
  have gv := good_slice hG 20 ((List.range 4).map fun k ↦
    Stmt.atom (.load (.n (43 + k)) (.n 17) (6 + k))) (by decide +kernel) (by decide +kernel)
  have kv : ∀ k < 4, some (43 + k, 17, 6 + k) ∉ lyS.map loadKey := by decide +kernel
  have rv : ∀ k < 4, ∀ w, LoadHolds rd (σ (.n 3)) (10 * L + (6 + k)) w →
      σ (.n (43 + k)) = w ∧ LoadHolds rd (σ (.n 17)) (6 + k) (σ (.n (43 + k))) := fun k hk w hw =>
    good_readS (gv _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)) (kv k hk)
      ((ld (6 + k) _).mpr hw)
  obtain ⟨e43, l43⟩ := rv 0 (by omega) _ (by rw [← Nat.add_assoc]; exact hval 0 (by omega))
  obtain ⟨e44, l44⟩ := rv 1 (by omega) _ (by rw [← Nat.add_assoc]; exact hval 1 (by omega))
  obtain ⟨e45, l45⟩ := rv 2 (by omega) _ (by rw [← Nat.add_assoc]; exact hval 2 (by omega))
  obtain ⟨e46, l46⟩ := rv 3 (by omega) _ hpos
  -- the point row and the first record
  have c47 : σ (.n 47) = word 2 0 := g 24 (.const (.n 47) (word 2 0)) (by decide +kernel)
  have m48 := good_mul (g 25 (.mul (.n 48) (.n 0) (.n 47)) (by decide +kernel)) (by omega)
    (by omega)
  have m49 := good_mul (g 26 (.mul (.n 49) (.n 48) (.n 48)) (by decide +kernel)) (by omega)
    (by omega)
  have m50 := good_mul (g 27 (.mul (.n 50) (.n 49) (.n 49)) (by decide +kernel)) (by omega)
    (by omega)
  have m51 := good_mul (g 28 (.mul (.n 51) (.n 50) (.n 48)) (by decide +kernel)) (by omega)
    (by omega)
  have m52 := good_mul (g 29 (.mul (.n 52) (.n 51) (.n 51)) (by decide +kernel)) (by omega)
    (by omega)
  have m53 := good_mul (g 30 (.mul (.n 53) (.n 52) (.n 52)) (by decide +kernel)) (by omega)
    (by omega)
  have m54 := good_mul (g 31 (.mul (.n 54) (.n 53) (.n 53)) (by decide +kernel)) (by omega)
    (by omega)
  have m55 := good_mul (g 32 (.mul (.n 55) (.n 5) (.n 54)) (by decide +kernel)) (by omega)
    (by omega)
  have m56 := good_mul (g 33 (.mul (.n 56) (.n 6) (.n 46)) (by decide +kernel)) (by omega)
    (by omega)
  have e55 : σ (.n 55) = σ (.n 5) * gen ^ (40 * (j + 1)) := by
    rw [m55, m54, m53, m52, m51, m50, m49, m48, c47, tb_word_gen, hx, ← pow_succ]
    ring
  have e56 : σ (.n 56) = σ (.n 6) * pos := by rw [m56, e46]
  have s37 : ∀ k < 5, LoadHolds rd (σ (.n 56)) (862 * k) (σ (.n (37 + k))) := by
    intro k hk
    have := tbCapAt_getD hc0 hk
    rw [show 0 + k * gkCap = 862 * k by unfold gkCap; ring] at this
    rw [e56, show 37 + k = 29 + (8 + k) by omega, hP (8 + k) (by omega)]
    rwa [Fs.squeeze, capOf_getD _ hk] at this
  have s23 : LoadHolds rd (σ (.n 56)) 4310 (σ (.n 23)) := by rw [e56, e23]; exact hu0
  have m57 := good_mul (g 40 (.mul (.n 57) (.n 42) (.n 45)) (by decide +kernel)) (by omega)
    (by omega)
  have a58 : σ (.n 58) = σ (.n 44) + σ (.n 57) := g 41 (.add (.n 58) (.n 44) (.n 57))
    (by decide +kernel)
  have m59 := good_mul (g 42 (.mul (.n 59) (.n 42) (.n 58)) (by decide +kernel)) (by omega)
    (by omega)
  have a60 : σ (.n 60) = σ (.n 43) + σ (.n 59) := g 43 (.add (.n 60) (.n 43) (.n 59))
    (by decide +kernel)
  have e60 : σ (.n 60) = polyEval st.values s.squeeze.1 := by
    obtain ⟨v0, v1, v2, hv3⟩ : ∃ v0 v1 v2, st.values = [v0, v1, v2] := by
      match st.values, hvl with
      | [v0, v1, v2], _ => exact ⟨v0, v1, v2, rfl⟩
    rw [a60, m59, a58, m57, e43, e44, e45, e42, hv3]
    simp only [polyEval, List.foldr, List.getD_cons_zero, List.getD_cons_succ]
    ring
  have s60 : LoadHolds rd (σ (.n 56)) 5172 (σ (.n 60)) := by rw [e56, e60]; exact hl0
  refine ⟨?_, e11, e12, e17, e42, e46, e55, e56, c25, c26, c27, c28⟩
  -- the region holds
  refine holdsList_straightN _ (by decide +kernel) ?_ trivial
  simp only [lyR1, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
    List.mem_range, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, and_assoc,
    keccakA, challengeT]
  refine ⟨m11, m12, m13, m14, m15, m16, m17, fun k hk => ?_, c24,
    show σ (.n 25) = word 0 0 by rw [c25, tb_word_zero],
    show σ (.n 26) = word 0 0 by rw [c26, tb_word_zero],
    show σ (.n 27) = word 0 0 by rw [c27, tb_word_zero],
    show σ (.n 28) = word 0 0 by rw [c28, tb_word_zero], k18, hco, fun k hk => ?_,
    c47, m48, m49, m50, m51, m52, m53, m54, m55, m56, fun k hk => s37 k hk,
    s23, m57, a58, m59, a60, s60⟩
  · rcases Nat.lt_or_ge k 5 with h5 | h5
    · exact (rcap k h5).2
    · rw [show k = 5 by omega]; exact l23
  · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · exact l43
    · exact l44
    · exact l45
    · exact l46

theorem tb_isInK_one : IsInK (1 : E) := by simpa using tb_gen_pow_isInK 0

/-- `n` rounds between records `1` apart, as B1-a's `GkrRoundsOut` on the record's cursor. -/
theorem gkOut_of_tbN {rd : Reader} {n : ℕ} {rec pt cur : E} (h : TbGkrRoundsOut n 1 rd rec pt)
    (hc : LoadHolds rd rec (5 * gkCap) cur) (hpad : n % 2 = 1 → LoadHolds rd pt (42 + n) 0) :
    GkrRoundsOut n rd rec pt cur := by
  obtain ⟨cap, cur', claim, cs, es, h1, hc', h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  obtain rfl := tb_loadHolds_unique hc' hc
  exact ⟨cap, claim, cs, es, h1, h3, h4, h5, h6, h7, h8, h9, hpad, h10, h11, h12⟩

/-- **The rounds**: `verify_bus_gkr_loop0_loop0` (`j` pairs of rounds), then `gkr_rounds__L2`, or
`gkr_rounds__L1` at an odd depth (its row's zero cell after the challenges), each from its
record. -/
theorem lyc_rounds (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {j sh : ℕ}
    (hj : j < 2 ^ 30) (hsh2 : sh < 2) (hx : σ (.n 0) = gen ^ j)
    (e11 : σ (.n 11) = gen ^ (2 * j)) (e8 : σ (.n 8) = gen ^ sh)
    (hT : ∀ y < j, TbGkrRoundsOut 2 1 rd (σ (.n 56) * gen ^ y) (σ (.n 55) * gen ^ (2 * y)))
    (hTl : TbGkrRoundsOut (2 - sh) 1 rd (σ (.n 56) * gen ^ j) (σ (.n 55) * gen ^ (2 * j)))
    (hpad : sh = 1 → LoadHolds rd (σ (.n 55) * gen ^ (2 * j)) 43 0) :
    Stmt.HoldsList (coreProgram.Rel rd) rd σ lyR2 True kret := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  have c61 : σ (.n 61) = word 1 0 := g 45 (.const (.n 61) (word 1 0)) (by decide +kernel)
  have a62 : σ (.n 62) = σ (.n 61) + σ (.n 0) := g 46 (.add (.n 62) (.n 61) (.n 0))
    (by decide +kernel)
  have c63 : σ (.n 63) = word 1 0 := g 47 (.const (.n 63) (word 1 0)) (by decide +kernel)
  have m64 := good_mul (g 49 (.mul (.n 64) (.n 56) (.n 0)) (by decide +kernel)) (by omega)
    (by omega)
  have c66 : σ (.n 66) = word 1 0 := g 51 (.const (.n 66) (word 1 0)) (by decide +kernel)
  have a67 : σ (.n 67) = σ (.n 8) + σ (.n 66) := g 52 (.add (.n 67) (.n 8) (.n 66))
    (by decide +kernel)
  have e64 : σ (.n 64) = σ (.n 56) * gen ^ j := by rw [m64, hx]
  obtain ⟨-, cur, -, -, -, -, hcur, -⟩ := id hTl
  obtain ⟨e65, l65⟩ := good_read (g 50 (.load (.n 65) (.n 64) 4310) (by decide +kernel))
    (by decide +kernel) (show LoadHolds rd (σ (.n 64)) 4310 cur by rw [e64]; exact hcur)
  have hcur65 : LoadHolds rd (σ (.n 64)) (5 * gkCap) (σ (.n 65)) := l65
  refine holdsList_of_vsh lyR2 (by decide +kernel) (fun s hs => ?_) trivial
  simp only [lyR2, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact c61
  · exact a62
  · exact c63
  · -- `verify_bus_gkr_loop0_loop0`
    refine ⟨by rw [a62, c61, tb_word_one, hx]; exact tb_isInK_add tb_isInK_one (tb_gen_pow_isInK _),
      fun hne => ?_⟩
    have hpos : 0 < j := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · rw [a62, c61, tb_word_one, hx, h0, pow_zero, e_add_self] at hne; exact absurd rfl hne
      · exact h0
    simp only [List.map_cons, List.map_nil, c63, tb_word_one, hx]
    exact l29_complete hpos (by omega) hT
  · exact m64
  · exact l65
  · exact c66
  · exact a67
  · -- the last rounds
    have gb := good_ite hG 53 (.n 67) ly72 ly71 (by decide +kernel)
    refine ⟨by rw [a67, c66, tb_word_one, e8]; exact tb_isInK_add (tb_gen_pow_isInK _) tb_isInK_one,
      fun h0 s hs => ?_, fun hne s hs => ?_⟩
    · have hsh0 : sh = 0 := by
        by_contra h
        rw [a67, c66, tb_word_one, e8, show sh = 1 by omega, pow_one] at h0
        have := gen_pow_inj (a := 1) (b := 0) (by omega) (by omega)
          ((pow_one gen).trans ((e_add_eq_zero_iff.mp h0).trans (pow_zero gen).symm))
        omega
      have m68 := good_mulS (gb (.atom (.mul (.n 68) (.n 55) (.n 11))) (by simp [ly72])) (by omega)
        (by omega)
      have e69 : σ (.n 69) = 0 := gb (.call "gkr_rounds__L2" [.n 64, .n 68, .n 65, .n 4, .n 9]
        [.n 69]) (by simp [ly72]) (.n 69) List.mem_cons_self
      simp only [ly72, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact m68
      · show coreProgram.Rel rd "gkr_rounds__L2"
          [σ (.n 64), σ (.n 68), σ (.n 65), σ (.n 4), σ (.n 9)] [σ (.n 69)]
        rw [hsh0, Nat.sub_zero] at hTl
        rw [e69]
        refine (gkr_rounds_holds 2 (by simp [gkrRoundsCounts]) rd _ _).mpr ⟨rfl, ?_⟩
        exact gkOut_of_tbN (by rw [e64, m68, e11]; exact hTl) hcur65 (fun h => absurd h (by decide))
    · have hsh1 : sh = 1 := by
        by_contra h
        rw [a67, c66, tb_word_one, e8, show sh = 0 by omega, pow_zero, e_add_self] at hne
        exact hne rfl
      have m70 := good_mulS (gb (.atom (.mul (.n 70) (.n 55) (.n 11))) (by simp [ly71])) (by omega)
        (by omega)
      have e71 : σ (.n 71) = 0 := gb (.call "gkr_rounds__L1" [.n 64, .n 70, .n 65, .n 4, .n 9]
        [.n 71]) (by simp [ly71]) (.n 71) List.mem_cons_self
      simp only [ly71, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact m70
      · show coreProgram.Rel rd "gkr_rounds__L1"
          [σ (.n 64), σ (.n 70), σ (.n 65), σ (.n 4), σ (.n 9)] [σ (.n 71)]
        rw [show 2 - sh = 1 by omega] at hTl
        rw [e71]
        refine (gkr_rounds_holds 1 (by simp [gkrRoundsCounts]) rd _ _).mpr ⟨rfl, ?_⟩
        exact gkOut_of_tbN (by rw [e64, m70, e11]; exact hTl) hcur65
          (fun _ => by rw [m70, e11]; exact hpad hsh1)

/-- **The last record**: its capacity and cursor, at `rec·g^(j + 1)`. -/
theorem lyc_last (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {j : ℕ}
    (hx : σ (.n 0) = gen ^ j) {cap : List E} {cur : E}
    (hc : TbCapAt rd (σ (.n 56) * gen ^ (j + 1)) 0 gkCap cap)
    (hu : LoadHolds rd (σ (.n 56) * gen ^ (j + 1)) (5 * gkCap) cur) :
    Stmt.HoldsList C rd σ lyR3 True kret ∧ σ (.n 74) = σ (.n 56) * gen ^ (j + 1) ∧
      (∀ k < 5, σ (.n (75 + k)) = cap.getD k 0) ∧ σ (.n 80) = cur := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  have m72 := good_mul (g 54 (.mul (.n 72) (.n 56) (.n 0)) (by decide +kernel)) (by omega)
    (by omega)
  have c73 : σ (.n 73) = word 2 0 := g 55 (.const (.n 73) (word 2 0)) (by decide +kernel)
  have m74 := good_mul (g 56 (.mul (.n 74) (.n 72) (.n 73)) (by decide +kernel)) (by omega)
    (by omega)
  have e74 : σ (.n 74) = σ (.n 56) * gen ^ (j + 1) := by
    rw [m74, m72, c73, tb_word_gen, hx, pow_succ, mul_assoc]
  have gc := good_slice hG 57 ((List.range 6).map fun k ↦
    Stmt.atom (.load (.n (75 + k)) (.n 74) (862 * k))) (by decide +kernel) (by decide +kernel)
  have kc : ∀ k < 6, some (75 + k, 74, 862 * k) ∉ lyS.map loadKey := by decide +kernel
  have rc : ∀ k < 5, σ (.n (75 + k)) = cap.getD k 0 ∧
      LoadHolds rd (σ (.n 74)) (862 * k) (σ (.n (75 + k))) := fun k hk =>
    good_readS (gc _ (List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩)) (kc k (by omega))
      (by have := tbCapAt_getD hc hk
          rwa [e74, show 862 * k = 0 + k * gkCap by unfold gkCap; ring])
  obtain ⟨e80, l80⟩ := good_readS (gc _ (List.mem_map.mpr ⟨5, List.mem_range.mpr (by omega),
    rfl⟩)) (kc 5 (by omega)) (by rw [e74]; exact hu)
  refine ⟨?_, e74, fun k hk => (rc k hk).1, e80⟩
  refine holdsList_straightN _ (by decide +kernel) ?_ trivial
  simp only [lyR3, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
    List.mem_range, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, and_assoc]
  refine ⟨m72, c73, m74, fun k hk => ?_⟩
  rcases Nat.lt_or_ge k 5 with h5 | h5
  · exact (rc k h5).2
  · rw [show k = 5 by omega]; exact l80

/-- **The children**: the twelve words at the last record's cursor, read, and absorbed four at a
time over the last record's capacity. -/
theorem lyc_children (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {cap : List E}
    (hcl : cap.length = 5) (e75 : ∀ k < 5, σ (.n (75 + k)) = cap.getD k 0) {ch : List E}
    (hch : ch.length = 12) (hr : TbReadsAt rd (σ (.n 80)) ch) :
    Stmt.HoldsList C rd σ lyR4 True kret ∧
      (∀ i < 12, σ (.n (lyEv i)) = ch.getD i 0 ∧ σ (.n (lyEv i + 3)) = σ (.n (lyEv i)) ∧
        FsPackOk σ (.n (lyEv i)) (lyEv i + 1) dsObserve) ∧
      (lyCap 126).map σ = capOf (Fs.perm ⟨capOf (Fs.perm ⟨cap, (lyCh σ 0).map (·, dsObserve)⟩),
        (lyCh σ 1).map (·, dsObserve)⟩) := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  have hni : ∀ i < 12, (lyEvT i).all notIteB = true := by decide +kernel
  have hk : ∀ i < 12, some (lyEv i, 80, i) ∉ lyS.map loadKey := by decide +kernel
  have EV : ∀ i < 12, (∀ s ∈ lyEvT i, SHolds C rd σ s) ∧
      σ (.n (lyEv i)) = ch.getD i 0 ∧ σ (.n (lyEv i + 3)) = σ (.n (lyEv i)) ∧
      FsPackOk σ (.n (lyEv i)) (lyEv i + 1) dsObserve := by
    intro i hi
    have gb := good_slice hG (lyPos i) (lyEvT i) (lyEvs_check i hi) (hni i hi)
    have hl : LoadHolds rd (σ (.n 80)) (0 + i) (ch.getD i 0) := by
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
  have hS0 : ((List.range 5).map fun k ↦ V.n (75 + k)).map σ = cap := by
    rw [tb_eq_map_getD hcl, List.map_map]
    apply List.map_congr_left
    intro k hk'
    exact e75 k (List.mem_range.mp hk')
  obtain ⟨k79, -⟩ := keccak_good (g 79 (.keccak (lyRate 0 ++ (List.range 5).map fun k ↦
    .n (75 + k)) (lyOuts 97) false false) (by decide +kernel))
  obtain ⟨-, B0⟩ := ly_perm_block (hp 0 (by omega)) k79
  rw [hS0] at B0
  obtain ⟨k96, -⟩ := keccak_good (g 96 (.keccak (lyRate 1 ++ lyCap 97) (lyOuts 126) false false)
    (by decide +kernel))
  obtain ⟨-, B1⟩ := ly_perm_block (hp 1 (by omega)) k96
  rw [B0] at B1
  refine ⟨?_, fun i hi => (EV i hi).2, B1⟩
  refine holdsList_straightN _ (by decide +kernel) ?_ trivial
  simp only [lyR4, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, and_true, and_assoc, keccakA]
  exact ⟨forall_flatten_range fun i hi => (EV i (by omega)).1, k79,
    forall_flatten_range fun i hi => (EV (4 + i) (by omega)).1, k96,
    forall_flatten_range fun i hi => (EV (8 + i) (by omega)).1⟩

/-- **The check and the two new coordinates**: the last claim, read at the last record, is the
children's products' polynomial at the combiner; the sponge after the twelve children squeezes the
two coordinates and leaves the capacity at `194 ..`. -/
theorem lyc_check (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {P1 : KeccakState}
    (cp : ∀ i < 12, σ (.n (lyEv i + 3)) = σ (.n (lyEv i)))
    (hpk : ∀ i < 12, FsPackOk σ (.n (lyEv i)) (lyEv i + 1) dsObserve)
    (hB1 : (lyCap 126).map σ = capOf P1) {claim : E}
    (hcl : LoadHolds rd (σ (.n 74)) 5172 claim)
    (hcheck : claim =
      polyEval [prodE (lyCh σ 0), prodE (lyCh σ 1), prodE (lyCh σ 2)] (σ (.n 42)))
    (c25 : σ (.n 25) = 0) (c26 : σ (.n 26) = 0) (c27 : σ (.n 27) = 0) (c28 : σ (.n 28) = 0) :
    Stmt.HoldsList C rd σ lyR5 True kret ∧
      σ (.n 185) = challengeOf (Fs.perm ⟨capOf P1, (lyCh σ 2).map (·, dsObserve)⟩) ∧
      σ (.n 199) = challengeOf (permOf (rateOf [] ++
        capOf (Fs.perm ⟨capOf P1, (lyCh σ 2).map (·, dsObserve)⟩))) ∧
      ((List.range 5).map fun k ↦ σ (.n (194 + k))) = capOf (permOf (rateOf [] ++
        capOf (Fs.perm ⟨capOf P1, (lyCh σ 2).map (·, dsObserve)⟩))) := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  obtain ⟨e155, l155⟩ := good_read (g 113 (.load (.n 155) (.n 74) 5172) (by decide +kernel))
    (by decide +kernel) hcl
  -- the check
  have m151 := good_mul (g 114 (.mul (.n 156) (.n 142) (.n 146)) (by decide +kernel)) (by omega)
    (by omega)
  have m152 := good_mul (g 115 (.mul (.n 157) (.n 156) (.n 150)) (by decide +kernel)) (by omega)
    (by omega)
  have m153 := good_mul (g 116 (.mul (.n 158) (.n 157) (.n 154)) (by decide +kernel)) (by omega)
    (by omega)
  have c154 : σ (.n 159) = word 0 0 := g 117 (.const (.n 159) (word 0 0)) (by decide +kernel)
  have m155 := good_mul (g 118 (.mul (.n 160) (.n 42) (.n 159)) (by decide +kernel)) (by omega)
    (by omega)
  have a156 : σ (.n 161) = σ (.n 158) + σ (.n 160) :=
    g 119 (.add (.n 161) (.n 158) (.n 160)) (by decide +kernel)
  have m157 := good_mul (g 120 (.mul (.n 162) (.n 113) (.n 117)) (by decide +kernel)) (by omega)
    (by omega)
  have m158 := good_mul (g 121 (.mul (.n 163) (.n 162) (.n 121)) (by decide +kernel)) (by omega)
    (by omega)
  have m159 := good_mul (g 122 (.mul (.n 164) (.n 163) (.n 125)) (by decide +kernel)) (by omega)
    (by omega)
  have m160 := good_mul (g 123 (.mul (.n 165) (.n 42) (.n 161)) (by decide +kernel)) (by omega)
    (by omega)
  have a161 : σ (.n 166) = σ (.n 164) + σ (.n 165) :=
    g 124 (.add (.n 166) (.n 164) (.n 165)) (by decide +kernel)
  have m162 := good_mul (g 125 (.mul (.n 167) (.n 84) (.n 88)) (by decide +kernel)) (by omega)
    (by omega)
  have m163 := good_mul (g 126 (.mul (.n 168) (.n 167) (.n 92)) (by decide +kernel)) (by omega)
    (by omega)
  have m164 := good_mul (g 127 (.mul (.n 169) (.n 168) (.n 96)) (by decide +kernel)) (by omega)
    (by omega)
  have m165 := good_mul (g 128 (.mul (.n 170) (.n 42) (.n 166)) (by decide +kernel)) (by omega)
    (by omega)
  have a166 : σ (.n 171) = σ (.n 169) + σ (.n 170) :=
    g 129 (.add (.n 171) (.n 169) (.n 170)) (by decide +kernel)
  have e166 : σ (.n 171) =
      polyEval [prodE (lyCh σ 0), prodE (lyCh σ 1), prodE (lyCh σ 2)] (σ (.n 42)) := by
    rw [a166, m165, a161, m160, a156, m155, c154, tb_word_zero, m153, m152, m151, m159, m158, m157,
      m164, m163, m162,
      show σ (.n 84) = σ (.n 81) from cp 0 (by omega), show σ (.n 88) = σ (.n 85) from cp 1 (by omega),
      show σ (.n 92) = σ (.n 89) from cp 2 (by omega),
      show σ (.n 96) = σ (.n 93) from cp 3 (by omega),
      show σ (.n 113) = σ (.n 110) from cp 4 (by omega),
      show σ (.n 117) = σ (.n 114) from cp 5 (by omega),
      show σ (.n 121) = σ (.n 118) from cp 6 (by omega),
      show σ (.n 125) = σ (.n 122) from cp 7 (by omega),
      show σ (.n 142) = σ (.n 139) from cp 8 (by omega),
      show σ (.n 146) = σ (.n 143) from cp 9 (by omega),
      show σ (.n 150) = σ (.n 147) from cp 10 (by omega),
      show σ (.n 154) = σ (.n 151) from cp 11 (by omega)]
    have hc0 : lyCh σ 0 = [σ (.n 81), σ (.n 85), σ (.n 89), σ (.n 93)] := by rw [lyCh_eq]; rfl
    have hc1 : lyCh σ 1 = [σ (.n 110), σ (.n 114), σ (.n 118), σ (.n 122)] := by rw [lyCh_eq]; rfl
    have hc2 : lyCh σ 2 = [σ (.n 139), σ (.n 143), σ (.n 147), σ (.n 151)] := by rw [lyCh_eq]; rfl
    rw [hc0, hc1, hc2]
    simp only [polyEval, prodE, List.foldr, List.foldl]
    ring
  -- the third block's permutation
  have hp2 : ∀ i < 4, FsPackOk σ (.n (lyEv (4 * 2 + i))) (lyEv (4 * 2 + i) + 1) dsObserve :=
    fun i hi => hpk (4 * 2 + i) (by omega)
  obtain ⟨k131, -⟩ := keccak_good (g 131 (.keccak (lyRate 2 ++ lyCap 126) (lyOuts 172) false false)
    (by decide +kernel))
  obtain ⟨P2, B2⟩ := ly_perm_block hp2 k131
  rw [hB1] at P2 B2
  set Q := Fs.perm ⟨capOf P1, (lyCh σ 2).map (·, dsObserve)⟩ with hQ
  -- the first coordinate
  have hco2 := challengeT_good (good_slice hG 132 (challengeT (.n 172) 185)
    (by decide +kernel) (by decide +kernel))
  have e185 : σ (.n 185) = challengeOf Q := challengeT_value hco2 (P2 0 (by omega))
  -- the second
  have hz : (([.n 25, .n 25, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28] ++ lyCap 172 : List V).map σ) =
      rateOf [] ++ capOf Q := by
    rw [ly_zero_rate c25 c26 c27 c28, B2]
  obtain ⟨k133, P3, B3⟩ := lyc_keccak (g 133 (.keccak ([.n 25, .n 25, .n 25, .n 25, .n 25, .n 26,
    .n 27, .n 28] ++ lyCap 172) (lyOuts 186) false false) (by decide +kernel))
  rw [hz] at P3 B3
  have hco3 := challengeT_good (good_slice hG 134 (challengeT (.n 186) 199)
    (by decide +kernel) (by decide +kernel))
  have e199 : σ (.n 199) = challengeOf (permOf (rateOf [] ++ capOf Q)) :=
    challengeT_value hco3 (P3 0 (by omega))
  refine ⟨?_, e185, e199, ?_⟩
  · refine holdsList_straightN _ (by decide +kernel) ?_ trivial
    simp only [lyR5, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true, and_assoc, keccakA, challengeT]
    exact ⟨l155, m151, m152, m153, c154, m155, a156, m157, m158, m159, m160, a161, m162, m163,
      m164, m165, a166, show σ (.n 155) + σ (.n 171) = 0 by rw [e155, hcheck, ← e166, e_add_self],
      k131, hco2, k133, hco3⟩
  · rw [← B3]
    simp [lyCap]

/-- A tree's new value on its equations: its four children's multilinear value at the two new
coordinates, stored at `off`. -/
theorem lyc_val (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {t b off : ℕ} (n : ℕ)
    (heq : tbStmtsEqb (lyValT t b off) ((lyPre.drop n).take (lyValT t b off).length) = true)
    (ht : t < 3) (hb : 199 < b)
    (hl : LoadHolds rd (σ (.n 17)) off (multilinearEval (lyCh σ t) [σ (.n 185), σ (.n 199)]))
    (cp : ∀ i < 12, σ (.n (lyEv i + 3)) = σ (.n (lyEv i))) :
    ∀ s ∈ lyValT t b off, SHolds C rd σ s := by
  have gb := good_slice hG n (lyValT t b off) heq (by simp [lyValT, chValT, notIteB])
  have he : ∀ i < 4, lyEv (4 * t + i) + 3 < b := by
    intro i hi; unfold lyEv chB; omega
  have a0 : σ (.n b) = σ (.n (lyEv (4 * t + 0) + 3)) + σ (.n (lyEv (4 * t + 1) + 3)) :=
    gb (.atom (.add (.n b) _ _)) (by simp [lyValT, chValT])
  have m1 := good_mulS (gb (.atom (.mul (.n (b + 1)) (.n 185) (.n b))) (by simp [lyValT, chValT]))
    (by omega) (by omega)
  have a2 : σ (.n (b + 2)) = σ (.n (lyEv (4 * t + 0) + 3)) + σ (.n (b + 1)) :=
    gb (.atom (.add (.n (b + 2)) _ _)) (by simp [lyValT, chValT])
  have a3 : σ (.n (b + 3)) = σ (.n (lyEv (4 * t + 2) + 3)) + σ (.n (lyEv (4 * t + 3) + 3)) :=
    gb (.atom (.add (.n (b + 3)) _ _)) (by simp [lyValT, chValT])
  have m4 := good_mulS (gb (.atom (.mul (.n (b + 4)) (.n 185) (.n (b + 3))))
    (by simp [lyValT, chValT])) (by omega) (by omega)
  have a5 : σ (.n (b + 5)) = σ (.n (lyEv (4 * t + 2) + 3)) + σ (.n (b + 4)) :=
    gb (.atom (.add (.n (b + 5)) _ _)) (by simp [lyValT, chValT])
  have a6 : σ (.n (b + 6)) = σ (.n (b + 2)) + σ (.n (b + 5)) :=
    gb (.atom (.add (.n (b + 6)) _ _)) (by simp [lyValT, chValT])
  have m7 := good_mulS (gb (.atom (.mul (.n (b + 7)) (.n 199) (.n (b + 6))))
    (by simp [lyValT, chValT])) (by omega) (by omega)
  have a8 : σ (.n (b + 8)) = σ (.n (b + 2)) + σ (.n (b + 7)) :=
    gb (.atom (.add (.n (b + 8)) _ _)) (by simp [lyValT, chValT])
  have e8 : σ (.n (b + 8)) = multilinearEval (lyCh σ t) [σ (.n 185), σ (.n 199)] := by
    rw [a8, m7, a6, a5, m4, a3, a2, m1, a0, cp (4 * t + 0) (by omega), cp (4 * t + 1) (by omega),
      cp (4 * t + 2) (by omega), cp (4 * t + 3) (by omega), lyCh_eq]
    simp only [multilinearEval, List.foldl, foldPairs, List.headD]
    ring_nf
  simp only [lyValT, chValT, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  exact ⟨a0, m1, a2, a3, m4, a5, a6, m7, a8, show LoadHolds rd (σ (.n 17)) off (σ (.n (b + 8))) by
    rw [e8]; exact hl⟩

/-- **The next slot and the next iteration**: the stores of the slot `20` words on and of the next
row's first two cells, and the call at `x·g` below the bound. -/
theorem lyc_stores (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s)
    (cp : ∀ i < 12, σ (.n (lyEv i + 3)) = σ (.n (lyEv i)))
    (s40 : LoadHolds rd (σ (.n 55)) 40 (σ (.n 185)))
    (s41 : LoadHolds rd (σ (.n 55)) 41 (σ (.n 199)))
    (s20 : ∀ k < 5, LoadHolds rd (σ (.n 17)) (20 + k) (σ (.n (194 + k))))
    (s25 : LoadHolds rd (σ (.n 17)) 25 (σ (.n 80) * gen ^ 12))
    (sv : ∀ t < 3, LoadHolds rd (σ (.n 17)) (26 + t)
      (multilinearEval (lyCh σ t) [σ (.n 185), σ (.n 199)]))
    (s29 : LoadHolds rd (σ (.n 17)) 29 (σ (.n 46) * σ (.n 0) * gen ^ 2))
    (hK : IsInK (σ (.n 0) * gen + σ (.n 1)))
    (hcall : σ (.n 0) * gen + σ (.n 1) ≠ 0 →
      C name% «verify_bus_gkr_loop0» [σ (.n 0) * gen, σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4),
        σ (.n 5), σ (.n 6), σ (.n 7), σ (.n 8), σ (.n 9), σ (.n 10)] []) :
    Stmt.HoldsList C rd σ lyR6 True kret := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  have c200 : σ (.n 200) = word 4096 0 := g 142 (.const (.n 200) (word 4096 0))
    (by decide +kernel)
  have m201 := good_mul (g 143 (.mul (.n 201) (.n 80) (.n 200)) (by decide +kernel)) (by omega)
    (by omega)
  have m229 := good_mul (g 175 (.mul (.n 229) (.n 46) (.n 0)) (by decide +kernel)) (by omega)
    (by omega)
  have c230 : σ (.n 230) = word 4 0 := g 176 (.const (.n 230) (word 4 0)) (by decide +kernel)
  have m231 := good_mul (g 177 (.mul (.n 231) (.n 229) (.n 230)) (by decide +kernel)) (by omega)
    (by omega)
  have c232 : σ (.n 232) = word 2 0 := g 179 (.const (.n 232) (word 2 0)) (by decide +kernel)
  have m233 := good_mul (g 180 (.mul (.n 233) (.n 0) (.n 232)) (by decide +kernel)) (by omega)
    (by omega)
  have a234 : σ (.n 234) = σ (.n 233) + σ (.n 1) :=
    g 181 (.add (.n 234) (.n 233) (.n 1)) (by decide +kernel)
  have c235 : σ (.n 235) = word 2 0 := g 182 (.const (.n 235) (word 2 0)) (by decide +kernel)
  have m236 := good_mul (g 183 (.mul (.n 236) (.n 0) (.n 235)) (by decide +kernel)) (by omega)
    (by omega)
  have w4096 : word 4096 0 = gen ^ 12 := by
    rw [show (4096 : ℕ) = 2 ^ 12 by norm_num, tb_word_two_pow (by norm_num)]
  have w4 : word 4 0 = gen ^ 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, tb_word_two_pow (by norm_num)]
  refine holdsList_straightN _ (by decide +kernel) ?_ trivial
  simp only [lyR6, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
    List.mem_range, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, and_assoc]
  refine ⟨s40, s41, fun k hk => s20 k hk, c200, m201,
    show LoadHolds rd (σ (.n 17)) 25 (σ (.n 201)) by rw [m201, c200, w4096]; exact s25,
    lyc_val hG 145 (by decide +kernel) (by omega) (by omega) (sv 0 (by omega)) cp,
    lyc_val hG 155 (by decide +kernel) (by omega) (by omega) (sv 1 (by omega)) cp,
    lyc_val hG 165 (by decide +kernel) (by omega) (by omega) (sv 2 (by omega)) cp,
    m229, c230, m231,
    show LoadHolds rd (σ (.n 17)) 29 (σ (.n 231)) by rw [m231, m229, c230, w4]; exact s29,
    c232, m233, a234, c235, m236,
    ⟨by rw [a234, m233, c232, tb_word_gen]; exact hK, fun hne => ?_⟩⟩
  show C name% «verify_bus_gkr_loop0» (List.map σ [.n 236, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6,
      .n 7, .n 8, .n 9, .n 10]) []
  simp only [List.map_cons, List.map_nil]
  rw [m236, c235, tb_word_gen]
  exact hcall (by rw [a234, m233, c232, tb_word_gen] at hne; exact hne)

end Eval

end
end LeanVM.Guest.B1.Tables
