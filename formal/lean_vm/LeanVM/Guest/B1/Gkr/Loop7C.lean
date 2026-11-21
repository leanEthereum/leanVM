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

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value LeanVM.Guest.B1
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

/-- The head: the layer record's pointer, the combiner, the first round record, `half`,
`parity`. -/
def lyR1 : List Stmt :=
  [.atom (.mul (.n 10) (.n 0) (.n 0)), .atom (.mul (.n 11) (.n 10) (.n 2)),
    .atom (.mul (.n 12) (.n 0) (.n 0)), .atom (.mul (.n 13) (.n 12) (.n 0)),
    .atom (.mul (.n 14) (.n 13) (.n 13)), .atom (.mul (.n 15) (.n 14) (.n 14)),
    .atom (.mul (.n 16) (.n 15) (.n 0)), .atom (.mul (.n 17) (.n 3) (.n 16))] ++
  (List.range 6).map (fun k ↦ .atom (.load (.n (18 + k)) (.n 17) k)) ++
  [.atom (.const (.n 24) (word 1 0)), .atom (.const (.n 25) (word 0 0)),
    .atom (.const (.n 26) (word 0 0)), .atom (.const (.n 27) (word 0 0)),
    .atom (.const (.n 28) (word 0 0)),
    keccakA ([.n 25, .n 25, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28] ++
      (List.range 5).map fun k ↦ .n (18 + k)) (lyOuts 29)] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (42 + k)) (.n 17) (6 + k))) ++
  [.atom (.mul (.n 47) (.n 5) (.n 46))] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (37 + k)) (.n 47) k)) ++
  [.atom (.load (.n 23) (.n 47) 5), .atom (.mul (.n 48) (.n 29) (.n 44)),
    .atom (.add (.n 49) (.n 43) (.n 48)), .atom (.mul (.n 50) (.n 29) (.n 49)),
    .atom (.add (.n 51) (.n 42) (.n 50)), .atom (.load (.n 51) (.n 47) 6),
    .atom (.load (.n 52) (.n 17) 11), .atom (.load (.n 53) (.n 17) 12),
    .atom (.const (.n 54) (word 1 0)), .atom (.add (.n 55) (.n 54) (.n 52)),
    .atom (.const (.n 56) (word 1 0))]

/-- The rounds. -/
def lyR2 : List Stmt :=
  [.callIf (.n 55) name% «verify_bus_gkr_loop0_loop0» [.n 56, .n 52, .n 47, .n 45, .n 4],
    .atom (.mul (.n 57) (.n 52) (.n 52)), .atom (.mul (.n 58) (.n 57) (.n 57)),
    .atom (.mul (.n 59) (.n 58) (.n 58)), .atom (.mul (.n 60) (.n 59) (.n 59)),
    .atom (.mul (.n 61) (.n 60) (.n 59)), .atom (.mul (.n 62) (.n 61) (.n 61)),
    .atom (.mul (.n 63) (.n 62) (.n 59)), .atom (.mul (.n 64) (.n 47) (.n 63)),
    .atom (.mul (.n 65) (.n 45) (.n 59)),
    .dispatch (.n 53) ["gkr_rounds__L0", "gkr_rounds__L2", "gkr_rounds__L4", "gkr_rounds__L6"]
      [.n 64, .n 65, .n 4] [.n 66],
    .atom (.const (.n 67) (word 1 0)), .atom (.add (.n 68) (.n 7) (.n 67)),
    .ite (.n 68) [] [.atom (.mul (.n 69) (.n 10) (.n 10)), .atom (.mul (.n 70) (.n 69) (.n 10)),
      .atom (.mul (.n 71) (.n 70) (.n 70)), .atom (.mul (.n 72) (.n 71) (.n 10)),
      .atom (.mul (.n 73) (.n 47) (.n 72)), .atom (.mul (.n 74) (.n 45) (.n 10)),
      .call "gkr_rounds__L1" [.n 73, .n 74, .n 4] [.n 75]]]

/-- The last round record. -/
def lyR3 : List Stmt :=
  [.atom (.mul (.n 76) (.n 11) (.n 11)), .atom (.mul (.n 77) (.n 76) (.n 11)),
    .atom (.mul (.n 78) (.n 77) (.n 77)), .atom (.mul (.n 79) (.n 78) (.n 11)),
    .atom (.mul (.n 80) (.n 47) (.n 79))] ++
  (List.range 6).map (fun k ↦ .atom (.load (.n (81 + k)) (.n 80) k))

/-- The children, four at a permutation. -/
def lyR4 : List Stmt :=
  ((List.range 4).map lyEvT).flatten ++
  [keccakA (lyRate 0 ++ (List.range 5).map fun k ↦ .n (81 + k)) (lyOuts 103)] ++
  ((List.range 4).map fun i ↦ lyEvT (4 + i)).flatten ++
  [keccakA (lyRate 1 ++ lyCap 103) (lyOuts 132)] ++
  ((List.range 4).map fun i ↦ lyEvT (8 + i)).flatten

/-- The last claim's check and the new coordinates. -/
def lyR5 : List Stmt :=
  [.atom (.load (.n 161) (.n 80) 6),
    .atom (.mul (.n 162) (.n 148) (.n 152)), .atom (.mul (.n 163) (.n 162) (.n 156)),
    .atom (.mul (.n 164) (.n 163) (.n 160)), .atom (.const (.n 165) (word 0 0)),
    .atom (.mul (.n 166) (.n 29) (.n 165)), .atom (.add (.n 167) (.n 164) (.n 166)),
    .atom (.mul (.n 168) (.n 119) (.n 123)), .atom (.mul (.n 169) (.n 168) (.n 127)),
    .atom (.mul (.n 170) (.n 169) (.n 131)), .atom (.mul (.n 171) (.n 29) (.n 167)),
    .atom (.add (.n 172) (.n 170) (.n 171)), .atom (.mul (.n 173) (.n 90) (.n 94)),
    .atom (.mul (.n 174) (.n 173) (.n 98)), .atom (.mul (.n 175) (.n 174) (.n 102)),
    .atom (.mul (.n 176) (.n 29) (.n 172)), .atom (.add (.n 177) (.n 175) (.n 176)),
    .atom (.assertEq (.n 161) (.n 177)),
    keccakA (lyRate 2 ++ lyCap 132) (lyOuts 178),
    keccakA ([.n 25, .n 25, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28] ++ lyCap 178) (lyOuts 191)]

/-- The next slot and the next iteration. -/
def lyR6 : List Stmt :=
  [.atom (.load (.n 178) (.n 45) 40), .atom (.load (.n 191) (.n 45) 41)] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (199 + k)) (.n 17) (13 + k))) ++
  [.atom (.const (.n 204) (word 4096 0)), .atom (.mul (.n 205) (.n 86) (.n 204)),
    .atom (.load (.n 205) (.n 17) 18)] ++
  lyValT 0 206 19 ++ lyValT 1 215 20 ++ lyValT 2 224 21 ++
  [.atom (.const (.n 233) (word 1099511627776 0)), .atom (.mul (.n 234) (.n 45) (.n 233)),
    .atom (.load (.n 234) (.n 17) 22), .atom (.mul (.n 235) (.n 46) (.n 79)),
    .atom (.const (.n 236) (word 128 0)), .atom (.mul (.n 237) (.n 235) (.n 236)),
    .atom (.load (.n 237) (.n 17) 23), .atom (.mul (.n 238) (.n 9) (.n 53)),
    .atom (.load (.n 239) (.n 238) 4), .atom (.mul (.n 240) (.n 52) (.n 239)),
    .atom (.load (.n 240) (.n 17) 24), .atom (.mul (.n 241) (.n 9) (.n 53)),
    .atom (.load (.n 242) (.n 241) 0), .atom (.load (.n 242) (.n 17) 25),
    .atom (.const (.n 243) (word 2 0)), .atom (.mul (.n 244) (.n 0) (.n 243)),
    .atom (.add (.n 245) (.n 244) (.n 1)), .atom (.const (.n 246) (word 2 0)),
    .atom (.mul (.n 247) (.n 0) (.n 246)),
    .callIf (.n 245) name% «verify_bus_gkr_loop0» [.n 247, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6,
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

/-- **The head**: the layer record's pointer `layers·g^(13 j)`, the combiner's permutation over
the record's capacity, the first round record stored (its capacity, cursor and combined claim),
`half` and `parity`. -/
theorem lyc_head (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {j sh : ℕ}
    (hx : σ (.n 0) = gen ^ j) (hsg : σ (.n 2) = gen ^ (2 - sh)) (hsh : sh < 2) {s : Fs}
    {cur : E} {st : GkrState} {row pos half parity : E}
    (hS : GkSlot rd (σ (.n 3)) (2 * j + 2 - sh) s cur st row pos half parity)
    (hc0 : TbCapAt rd (σ (.n 5) * pos) 0 1 s.squeeze.2.cap)
    (hu0 : LoadHolds rd (σ (.n 5) * pos) 5 cur)
    (hl0 : LoadHolds rd (σ (.n 5) * pos) 6 (polyEval st.values s.squeeze.1)) :
    Stmt.HoldsList C rd σ lyR1 True kret ∧ σ (.n 10) = gen ^ (2 * j) ∧
      σ (.n 11) = gen ^ (2 * j + 2 - sh) ∧
      σ (.n 17) = σ (.n 3) * gen ^ (13 * j) ∧
      σ (.n 29) = s.squeeze.1 ∧ σ (.n 45) = row ∧ σ (.n 46) = pos ∧
      σ (.n 47) = σ (.n 5) * pos ∧ σ (.n 52) = half ∧ σ (.n 53) = parity ∧
      σ (.n 55) = 1 + half ∧ σ (.n 56) = 1 ∧ σ (.n 25) = 0 ∧ σ (.n 26) = 0 ∧
      σ (.n 27) = 0 ∧ σ (.n 28) = 0 := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  obtain ⟨hcl, hcap, hpe, hcur, hvl, hval, hrow, -, -, hpos, hhalf, hpar⟩ := hS
  set L := 2 * j + 2 - sh with hL
  have m10 := good_mul (g 0 (.mul (.n 10) (.n 0) (.n 0)) (by decide +kernel)) (by omega) (by omega)
  have m11 := good_mul (g 1 (.mul (.n 11) (.n 10) (.n 2)) (by decide +kernel)) (by omega) (by omega)
  have m12 := good_mul (g 2 (.mul (.n 12) (.n 0) (.n 0)) (by decide +kernel)) (by omega)
    (by omega)
  have m13 := good_mul (g 3 (.mul (.n 13) (.n 12) (.n 0)) (by decide +kernel)) (by omega)
    (by omega)
  have m14 := good_mul (g 4 (.mul (.n 14) (.n 13) (.n 13)) (by decide +kernel)) (by omega)
    (by omega)
  have m15 := good_mul (g 5 (.mul (.n 15) (.n 14) (.n 14)) (by decide +kernel)) (by omega)
    (by omega)
  have m16 := good_mul (g 6 (.mul (.n 16) (.n 15) (.n 0)) (by decide +kernel)) (by omega)
    (by omega)
  have m17 := good_mul (g 7 (.mul (.n 17) (.n 3) (.n 16)) (by decide +kernel)) (by omega) (by omega)
  have e10 : σ (.n 10) = gen ^ (2 * j) := by rw [m10, hx, ← pow_add]; ring_nf
  have e11 : σ (.n 11) = gen ^ L := by
    rw [m11, e10, hsg, ← pow_add, show 2 * j + (2 - sh) = L by omega]
  have e17 : σ (.n 17) = σ (.n 3) * gen ^ (13 * j) := by
    rw [m17, m16, m15, m14, m13, m12, hx]
    ring
  have hjL : (L - 1) / 2 = j := by omega
  have ld : ∀ k w, LoadHolds rd (σ (.n 17)) k w ↔
      LoadHolds rd (σ (.n 3)) (13 * ((L - 1) / 2) + k) w := by
    intro k w; rw [e17, tb_loadHolds_mul_gen_pow, hjL]
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
  have e42 : σ (.n 29) = s.squeeze.1 := challengeT_value (s0 := .n 29) (b := 29) rfl (hP 0 (by omega))
  -- the values, the row, the position, the first record
  have gv := good_slice hG 20 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (42 + k)) (.n 17) (6 + k))) (by decide +kernel) (by decide +kernel)
  have kv : ∀ k < 5, some (42 + k, 17, 6 + k) ∉ lyS.map loadKey := by decide +kernel
  have rv : ∀ k < 5, ∀ w, LoadHolds rd (σ (.n 3)) (13 * ((L - 1) / 2) + (6 + k)) w →
      σ (.n (42 + k)) = w ∧ LoadHolds rd (σ (.n 17)) (6 + k) (σ (.n (42 + k))) := fun k hk w hw =>
    good_readS (gv _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)) (kv k hk)
      ((ld (6 + k) _).mpr hw)
  obtain ⟨e43, l43⟩ := rv 0 (by omega) _ (by rw [← Nat.add_assoc]; exact hval 0 (by omega))
  obtain ⟨e44, l44⟩ := rv 1 (by omega) _ (by rw [← Nat.add_assoc]; exact hval 1 (by omega))
  obtain ⟨e45, l45⟩ := rv 2 (by omega) _ (by rw [← Nat.add_assoc]; exact hval 2 (by omega))
  obtain ⟨e46, l46⟩ := rv 3 (by omega) _ hrow
  obtain ⟨e47, l47⟩ := rv 4 (by omega) _ hpos
  have m48 := good_mul (g 25 (.mul (.n 47) (.n 5) (.n 46)) (by decide +kernel)) (by omega)
    (by omega)
  rw [e47] at m48
  have s37 : ∀ k < 5, LoadHolds rd (σ (.n 47)) k (σ (.n (37 + k))) := by
    intro k hk
    have := tbCapAt_getD hc0 hk
    rw [show 0 + k * 1 = k by ring] at this
    rw [m48, show 37 + k = 29 + (8 + k) by omega, hP (8 + k) (by omega)]
    rwa [Fs.squeeze, capOf_getD _ hk] at this
  have s23 : LoadHolds rd (σ (.n 47)) 5 (σ (.n 23)) := by rw [m48, e23]; exact hu0
  have m49 := good_mul (g 32 (.mul (.n 48) (.n 29) (.n 44)) (by decide +kernel)) (by omega)
    (by omega)
  have a50 : σ (.n 49) = σ (.n 43) + σ (.n 48) := g 33 (.add (.n 49) (.n 43) (.n 48))
    (by decide +kernel)
  have m51 := good_mul (g 34 (.mul (.n 50) (.n 29) (.n 49)) (by decide +kernel)) (by omega)
    (by omega)
  have a52 : σ (.n 51) = σ (.n 42) + σ (.n 50) := g 35 (.add (.n 51) (.n 42) (.n 50))
    (by decide +kernel)
  have e52 : σ (.n 51) = polyEval st.values s.squeeze.1 := by
    obtain ⟨v0, v1, v2, hv3⟩ : ∃ v0 v1 v2, st.values = [v0, v1, v2] := by
      match st.values, hvl with
      | [v0, v1, v2], _ => exact ⟨v0, v1, v2, rfl⟩
    rw [a52, m51, a50, m49, e43, e44, e45, e42, hv3]
    simp only [polyEval, List.foldr, List.getD_cons_zero, List.getD_cons_succ]
    ring
  have s52 : LoadHolds rd (σ (.n 47)) 6 (σ (.n 51)) := by rw [m48, e52]; exact hl0
  obtain ⟨e53, l53⟩ := good_read (g 37 (.load (.n 52) (.n 17) 11) (by decide +kernel))
    (by decide +kernel) ((ld 11 _).mpr hhalf)
  obtain ⟨e54, l54⟩ := good_read (g 38 (.load (.n 53) (.n 17) 12) (by decide +kernel))
    (by decide +kernel) ((ld 12 _).mpr hpar)
  have c55 : σ (.n 54) = word 1 0 := g 39 (.const (.n 54) (word 1 0)) (by decide +kernel)
  have a56 : σ (.n 55) = σ (.n 54) + σ (.n 52) := g 40 (.add (.n 55) (.n 54) (.n 52))
    (by decide +kernel)
  have c57 : σ (.n 56) = word 1 0 := g 41 (.const (.n 56) (word 1 0)) (by decide +kernel)
  rw [tb_word_one] at c24 c55 c57
  refine ⟨?_, e10, e11, e17, e42, e46, e47, m48, e53, e54, by rw [a56, c55, e53], c57, c25, c26,
    c27, c28⟩
  -- the region holds
  refine holdsList_straightN _ (by decide +kernel) ?_ trivial
  simp only [lyR1, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
    List.mem_range, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, and_assoc,
    keccakA]
  refine ⟨m10, m11, m12, m13, m14, m15, m16, m17, fun k hk => ?_,
    show σ (.n 24) = word 1 0 by rw [c24, tb_word_one],
    show σ (.n 25) = word 0 0 by rw [c25, tb_word_zero],
    show σ (.n 26) = word 0 0 by rw [c26, tb_word_zero],
    show σ (.n 27) = word 0 0 by rw [c27, tb_word_zero],
    show σ (.n 28) = word 0 0 by rw [c28, tb_word_zero], k19, fun k hk => ?_,
    show σ (.n 47) = σ (.n 5) * σ (.n 46) by rw [m48, e47], fun k hk => s37 k hk,
    s23, m49, a50, m51, a52, s52, l53, l54, show σ (.n 54) = word 1 0 by rw [c55, tb_word_one],
    a56, show σ (.n 56) = word 1 0 by rw [c57, tb_word_one]⟩
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
when the records (`7` words each) hold every run of consecutive rounds. -/
theorem lyc_rounds (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {j k sh : ℕ}
    (hj : j < 2 ^ 30) (hsh2 : sh < 2) (hk : k = j + 1 - sh)
    (e10 : σ (.n 10) = gen ^ (2 * j)) (e7 : σ (.n 7) = gen ^ sh)
    (e53 : σ (.n 52) = gen ^ (k / 4)) (e54 : σ (.n 53) = gen ^ (k % 4))
    (e56 : σ (.n 55) = 1 + gen ^ (k / 4)) (e57 : σ (.n 56) = 1)
    (hT : ∀ a k', a + k' ≤ 2 * k + sh →
      TbGkrRoundsOut k' rd (σ (.n 47) * gen ^ (7 * a)) (σ (.n 45) * gen ^ a)) :
    Stmt.HoldsList (coreProgram.Rel rd) rd σ lyR2 True kret := by
  have m57 := good_mul (ly_good hG 43 (.mul (.n 57) (.n 52) (.n 52)) (by decide +kernel))
    (by omega) (by omega)
  have m58 := good_mul (ly_good hG 44 (.mul (.n 58) (.n 57) (.n 57)) (by decide +kernel))
    (by omega) (by omega)
  have m59 := good_mul (ly_good hG 45 (.mul (.n 59) (.n 58) (.n 58)) (by decide +kernel))
    (by omega) (by omega)
  have m60 := good_mul (ly_good hG 46 (.mul (.n 60) (.n 59) (.n 59)) (by decide +kernel))
    (by omega) (by omega)
  have m61 := good_mul (ly_good hG 47 (.mul (.n 61) (.n 60) (.n 59)) (by decide +kernel))
    (by omega) (by omega)
  have m62 := good_mul (ly_good hG 48 (.mul (.n 62) (.n 61) (.n 61)) (by decide +kernel))
    (by omega) (by omega)
  have m63 := good_mul (ly_good hG 49 (.mul (.n 63) (.n 62) (.n 59)) (by decide +kernel))
    (by omega) (by omega)
  have m64 := good_mul (ly_good hG 50 (.mul (.n 64) (.n 47) (.n 63)) (by decide +kernel))
    (by omega) (by omega)
  have m65 := good_mul (ly_good hG 51 (.mul (.n 65) (.n 45) (.n 59)) (by decide +kernel))
    (by omega) (by omega)
  have e59 : σ (.n 59) = gen ^ (8 * (k / 4)) := by
    rw [m59, m58, m57, e53]; ring
  have e63 : σ (.n 63) = gen ^ (7 * (8 * (k / 4))) := by
    rw [m63, m62, m61, m60, e59]; ring
  have c67 : σ (.n 67) = word 1 0 := ly_good hG 53 (.const (.n 67) (word 1 0)) (by decide +kernel)
  have a68 : σ (.n 68) = σ (.n 7) + σ (.n 67) :=
    ly_good hG 54 (.add (.n 68) (.n 7) (.n 67)) (by decide +kernel)
  rw [tb_word_one] at c67
  refine holdsList_of_vsh lyR2 (by decide +kernel) (fun s hs => ?_) trivial
  simp only [lyR2, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- `verify_bus_gkr_loop0_loop0`
    refine ⟨by rw [e56]; exact tb_isInK_add tb_isInK_one (tb_gen_pow_isInK _), fun hne => ?_⟩
    have hpos : 0 < k / 4 := by
      rcases Nat.eq_zero_or_pos (k / 4) with h0 | h0
      · rw [e56, h0, pow_zero, e_add_self] at hne; exact absurd rfl hne
      · exact h0
    simp only [List.map_cons, List.map_nil, e57, e53]
    exact l29_complete hpos (by omega) fun i hi => by
      have := hT (8 * i) 8 (by omega)
      rwa [show 7 * (8 * i) = 56 * i by ring] at this
  · exact m57
  · exact m58
  · exact m59
  · exact m60
  · exact m61
  · exact m62
  · exact m63
  · exact m64
  · exact m65
  · -- `gkr_rounds__L{2r}`, `r = k % 4`
    have gd := good_slice hG 52 [.dispatch (.n 53)
      ["gkr_rounds__L0", "gkr_rounds__L2", "gkr_rounds__L4", "gkr_rounds__L6"] [.n 64, .n 65, .n 4]
      [.n 66]] (by decide +kernel) rfl _ List.mem_cons_self
    have e66 : σ (.n 66) = 0 := gd (.n 66) List.mem_cons_self
    have hr : k % 4 < 4 := Nat.mod_lt _ (by omega)
    refine ⟨k % 4, by simpa using hr, by rw [e54, gen_pow_eq_ofK], ?_⟩
    simp only [List.map_cons, List.map_nil, e66]
    rw [m64, m65, e63, e59]
    have hR := hT (8 * (k / 4)) (2 * (k % 4)) (by omega)
    have hr4 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    rcases hr4 with h | h | h | h <;> simp only [h, List.getElem_cons_zero,
      List.getElem_cons_succ] <;> rw [h] at hR
    · exact (gkr_rounds_holds.2 rd _ _).mpr rfl
    · exact (gkr_rounds_holds.1 2 (by simp [gkrRoundsCounts]) rd _ _).mpr ⟨rfl, hR⟩
    · exact (gkr_rounds_holds.1 4 (by simp [gkrRoundsCounts]) rd _ _).mpr ⟨rfl, hR⟩
    · exact (gkr_rounds_holds.1 6 (by simp [gkrRoundsCounts]) rd _ _).mpr ⟨rfl, hR⟩
  · exact c67.trans tb_word_one.symm
  · exact a68
  · -- `gkr_rounds__L1` at an odd depth
    have gb := good_ite hG 55 (.n 68) [] [.atom (.mul (.n 69) (.n 10) (.n 10)),
      .atom (.mul (.n 70) (.n 69) (.n 10)), .atom (.mul (.n 71) (.n 70) (.n 70)),
      .atom (.mul (.n 72) (.n 71) (.n 10)), .atom (.mul (.n 73) (.n 47) (.n 72)),
      .atom (.mul (.n 74) (.n 45) (.n 10)), .call "gkr_rounds__L1" [.n 73, .n 74, .n 4] [.n 75]]
      (by decide +kernel)
    refine ⟨by rw [a68, c67, e7]; exact tb_isInK_add (tb_gen_pow_isInK _) tb_isInK_one,
      fun _ s hs => absurd hs (by simp), fun hne s hs => ?_⟩
    have hsh1 : sh = 1 := by
      by_contra h
      rw [a68, c67, e7, show sh = 0 by omega, pow_zero, e_add_self] at hne
      exact hne rfl
    have m69 := good_mulS (gb (.atom (.mul (.n 69) (.n 10) (.n 10))) (by simp)) (by omega)
      (by omega)
    have m70 := good_mulS (gb (.atom (.mul (.n 70) (.n 69) (.n 10))) (by simp)) (by omega)
      (by omega)
    have m71 := good_mulS (gb (.atom (.mul (.n 71) (.n 70) (.n 70))) (by simp)) (by omega)
      (by omega)
    have m72 := good_mulS (gb (.atom (.mul (.n 72) (.n 71) (.n 10))) (by simp)) (by omega)
      (by omega)
    have m73 := good_mulS (gb (.atom (.mul (.n 73) (.n 47) (.n 72))) (by simp)) (by omega)
      (by omega)
    have m74 := good_mulS (gb (.atom (.mul (.n 74) (.n 45) (.n 10))) (by simp)) (by omega)
      (by omega)
    have e75 : σ (.n 75) = 0 :=
      gb (.call "gkr_rounds__L1" [.n 73, .n 74, .n 4] [.n 75]) (by simp) (.n 75) List.mem_cons_self
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact m69
    · exact m70
    · exact m71
    · exact m72
    · exact m73
    · exact m74
    · show coreProgram.Rel rd "gkr_rounds__L1" [σ (.n 73), σ (.n 74), σ (.n 4)] [σ (.n 75)]
      have e72 : σ (.n 72) = gen ^ (7 * (2 * j)) := by
        rw [m72, m71, m70, m69, e10]; ring
      rw [m73, m74, e72, e10, e75]
      exact (gkr_rounds_holds.1 1 (by simp [gkrRoundsCounts]) rd _ _).mpr
        ⟨rfl, hT (2 * j) 1 (by omega)⟩

/-- **The last round record**: its capacity and cursor, at `rec·g^(7L)`. -/
theorem lyc_last (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {L : ℕ}
    (e11 : σ (.n 11) = gen ^ L) {cap : List E} {cur : E}
    (hc : TbCapAt rd (σ (.n 47) * gen ^ (7 * L)) 0 1 cap)
    (hu : LoadHolds rd (σ (.n 47) * gen ^ (7 * L)) 5 cur) :
    Stmt.HoldsList C rd σ lyR3 True kret ∧ σ (.n 79) = gen ^ (7 * L) ∧
      σ (.n 80) = σ (.n 47) * gen ^ (7 * L) ∧
      (∀ k < 5, σ (.n (81 + k)) = cap.getD k 0) ∧ σ (.n 86) = cur := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  have m76 := good_mul (g 56 (.mul (.n 76) (.n 11) (.n 11)) (by decide +kernel)) (by omega)
    (by omega)
  have m77 := good_mul (g 57 (.mul (.n 77) (.n 76) (.n 11)) (by decide +kernel)) (by omega)
    (by omega)
  have m78 := good_mul (g 58 (.mul (.n 78) (.n 77) (.n 77)) (by decide +kernel)) (by omega)
    (by omega)
  have m79 := good_mul (g 59 (.mul (.n 79) (.n 78) (.n 11)) (by decide +kernel)) (by omega)
    (by omega)
  have m80 := good_mul (g 60 (.mul (.n 80) (.n 47) (.n 79)) (by decide +kernel)) (by omega)
    (by omega)
  have e79 : σ (.n 79) = gen ^ (7 * L) := by rw [m79, m78, m77, m76, e11]; ring
  have e80 : σ (.n 80) = σ (.n 47) * gen ^ (7 * L) := by rw [m80, e79]
  have gc := good_slice hG 61 ((List.range 6).map fun k ↦
    Stmt.atom (.load (.n (81 + k)) (.n 80) k)) (by decide +kernel) (by decide +kernel)
  have kc : ∀ k < 6, some (81 + k, 80, k) ∉ lyS.map loadKey := by decide +kernel
  have rc : ∀ k < 5, σ (.n (81 + k)) = cap.getD k 0 ∧
      LoadHolds rd (σ (.n 80)) k (σ (.n (81 + k))) := fun k hk =>
    good_readS (gc _ (List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩)) (kc k (by omega))
      (by have := tbCapAt_getD hc hk
          rw [show 0 + k * 1 = k by ring] at this
          rwa [e80])
  obtain ⟨e86, l86⟩ := good_readS (gc _ (List.mem_map.mpr ⟨5, List.mem_range.mpr (by omega),
    rfl⟩)) (kc 5 (by omega)) (by rw [e80]; exact hu)
  refine ⟨?_, e79, e80, fun k hk => (rc k hk).1, e86⟩
  refine holdsList_straightN _ (by decide +kernel) ?_ trivial
  simp only [lyR3, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
    List.mem_range, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, and_assoc]
  refine ⟨m76, m77, m78, m79, m80, fun k hk => ?_⟩
  rcases Nat.lt_or_ge k 5 with h5 | h5
  · exact (rc k h5).2
  · rw [show k = 5 by omega]; exact l86

/-- **The children**: the twelve words at the last record's cursor, read, and absorbed four at a
time over the last record's capacity. -/
theorem lyc_children (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {cap : List E}
    (hcl : cap.length = 5) (e70 : ∀ k < 5, σ (.n (81 + k)) = cap.getD k 0) {ch : List E}
    (hch : ch.length = 12) (hr : TbReadsAt rd (σ (.n 86)) ch) :
    Stmt.HoldsList C rd σ lyR4 True kret ∧
      (∀ i < 12, σ (.n (lyEv i)) = ch.getD i 0 ∧ σ (.n (lyEv i + 3)) = σ (.n (lyEv i)) ∧
        FsPackOk σ (.n (lyEv i)) (lyEv i + 1) dsObserve) ∧
      (lyCap 132).map σ = capOf (Fs.perm ⟨capOf (Fs.perm ⟨cap, (lyCh σ 0).map (·, dsObserve)⟩),
        (lyCh σ 1).map (·, dsObserve)⟩) := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  have hni : ∀ i < 12, (lyEvT i).all notIteB = true := by decide +kernel
  have hk : ∀ i < 12, some (lyEv i, 86, i) ∉ lyS.map loadKey := by decide +kernel
  have EV : ∀ i < 12, (∀ s ∈ lyEvT i, SHolds C rd σ s) ∧
      σ (.n (lyEv i)) = ch.getD i 0 ∧ σ (.n (lyEv i + 3)) = σ (.n (lyEv i)) ∧
      FsPackOk σ (.n (lyEv i)) (lyEv i + 1) dsObserve := by
    intro i hi
    have gb := good_slice hG (lyPos i) (lyEvT i) (lyEvs_check i hi) (hni i hi)
    have hl : LoadHolds rd (σ (.n 86)) (0 + i) (ch.getD i 0) := by
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
  have hS0 : ((List.range 5).map fun k ↦ V.n (81 + k)).map σ = cap := by
    rw [tb_eq_map_getD hcl, List.map_map]
    apply List.map_congr_left
    intro k hk'
    exact e70 k (List.mem_range.mp hk')
  obtain ⟨k76, -⟩ := keccak_good (g 83 (.keccak (lyRate 0 ++ (List.range 5).map fun k ↦
    .n (81 + k)) (lyOuts 103) false false) (by decide +kernel))
  obtain ⟨-, B0⟩ := ly_perm_block (hp 0 (by omega)) k76
  rw [hS0] at B0
  obtain ⟨k93, -⟩ := keccak_good (g 100 (.keccak (lyRate 1 ++ lyCap 103) (lyOuts 132) false false)
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
    (hB1 : (lyCap 132).map σ = capOf P1) {claim : E}
    (hcl : LoadHolds rd (σ (.n 80)) 6 claim)
    (hcheck : claim =
      polyEval [prodE (lyCh σ 0), prodE (lyCh σ 1), prodE (lyCh σ 2)] (σ (.n 29)))
    (c25 : σ (.n 25) = 0) (c26 : σ (.n 26) = 0) (c27 : σ (.n 27) = 0) (c28 : σ (.n 28) = 0) :
    Stmt.HoldsList C rd σ lyR5 True kret ∧
      σ (.n 178) = challengeOf (Fs.perm ⟨capOf P1, (lyCh σ 2).map (·, dsObserve)⟩) ∧
      σ (.n 191) = challengeOf (permOf (rateOf [] ++
        capOf (Fs.perm ⟨capOf P1, (lyCh σ 2).map (·, dsObserve)⟩))) ∧
      ((List.range 5).map fun k ↦ σ (.n (199 + k))) = capOf (permOf (rateOf [] ++
        capOf (Fs.perm ⟨capOf P1, (lyCh σ 2).map (·, dsObserve)⟩))) := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  obtain ⟨e150, l150⟩ := good_read (g 117 (.load (.n 161) (.n 80) 6) (by decide +kernel))
    (by decide +kernel) hcl
  -- the check
  have m151 := good_mul (g 118 (.mul (.n 162) (.n 148) (.n 152)) (by decide +kernel)) (by omega)
    (by omega)
  have m152 := good_mul (g 119 (.mul (.n 163) (.n 162) (.n 156)) (by decide +kernel)) (by omega)
    (by omega)
  have m153 := good_mul (g 120 (.mul (.n 164) (.n 163) (.n 160)) (by decide +kernel)) (by omega)
    (by omega)
  have c154 : σ (.n 165) = word 0 0 := g 121 (.const (.n 165) (word 0 0)) (by decide +kernel)
  have m155 := good_mul (g 122 (.mul (.n 166) (.n 29) (.n 165)) (by decide +kernel)) (by omega)
    (by omega)
  have a156 : σ (.n 167) = σ (.n 164) + σ (.n 166) :=
    g 123 (.add (.n 167) (.n 164) (.n 166)) (by decide +kernel)
  have m157 := good_mul (g 124 (.mul (.n 168) (.n 119) (.n 123)) (by decide +kernel)) (by omega)
    (by omega)
  have m158 := good_mul (g 125 (.mul (.n 169) (.n 168) (.n 127)) (by decide +kernel)) (by omega)
    (by omega)
  have m159 := good_mul (g 126 (.mul (.n 170) (.n 169) (.n 131)) (by decide +kernel)) (by omega)
    (by omega)
  have m160 := good_mul (g 127 (.mul (.n 171) (.n 29) (.n 167)) (by decide +kernel)) (by omega)
    (by omega)
  have a161 : σ (.n 172) = σ (.n 170) + σ (.n 171) :=
    g 128 (.add (.n 172) (.n 170) (.n 171)) (by decide +kernel)
  have m162 := good_mul (g 129 (.mul (.n 173) (.n 90) (.n 94)) (by decide +kernel)) (by omega)
    (by omega)
  have m163 := good_mul (g 130 (.mul (.n 174) (.n 173) (.n 98)) (by decide +kernel)) (by omega)
    (by omega)
  have m164 := good_mul (g 131 (.mul (.n 175) (.n 174) (.n 102)) (by decide +kernel)) (by omega)
    (by omega)
  have m165 := good_mul (g 132 (.mul (.n 176) (.n 29) (.n 172)) (by decide +kernel)) (by omega)
    (by omega)
  have a166 : σ (.n 177) = σ (.n 175) + σ (.n 176) :=
    g 133 (.add (.n 177) (.n 175) (.n 176)) (by decide +kernel)
  have e166 : σ (.n 177) =
      polyEval [prodE (lyCh σ 0), prodE (lyCh σ 1), prodE (lyCh σ 2)] (σ (.n 29)) := by
    rw [a166, m165, a161, m160, a156, m155, c154, tb_word_zero, m153, m152, m151, m159, m158, m157,
      m164, m163, m162,
      show σ (.n 90) = σ (.n 87) from cp 0 (by omega), show σ (.n 94) = σ (.n 91) from cp 1 (by omega),
      show σ (.n 98) = σ (.n 95) from cp 2 (by omega),
      show σ (.n 102) = σ (.n 99) from cp 3 (by omega),
      show σ (.n 119) = σ (.n 116) from cp 4 (by omega),
      show σ (.n 123) = σ (.n 120) from cp 5 (by omega),
      show σ (.n 127) = σ (.n 124) from cp 6 (by omega),
      show σ (.n 131) = σ (.n 128) from cp 7 (by omega),
      show σ (.n 148) = σ (.n 145) from cp 8 (by omega),
      show σ (.n 152) = σ (.n 149) from cp 9 (by omega),
      show σ (.n 156) = σ (.n 153) from cp 10 (by omega),
      show σ (.n 160) = σ (.n 157) from cp 11 (by omega)]
    have hc0 : lyCh σ 0 = [σ (.n 87), σ (.n 91), σ (.n 95), σ (.n 99)] := by rw [lyCh_eq]; rfl
    have hc1 : lyCh σ 1 = [σ (.n 116), σ (.n 120), σ (.n 124), σ (.n 128)] := by rw [lyCh_eq]; rfl
    have hc2 : lyCh σ 2 = [σ (.n 145), σ (.n 149), σ (.n 153), σ (.n 157)] := by rw [lyCh_eq]; rfl
    rw [hc0, hc1, hc2]
    simp only [polyEval, prodE, List.foldr, List.foldl]
    ring
  -- the third block's permutation
  have hp2 : ∀ i < 4, FsPackOk σ (.n (lyEv (4 * 2 + i))) (lyEv (4 * 2 + i) + 1) dsObserve :=
    fun i hi => hpk (4 * 2 + i) (by omega)
  obtain ⟨k128, -⟩ := keccak_good (g 135 (.keccak (lyRate 2 ++ lyCap 132) (lyOuts 178) false false)
    (by decide +kernel))
  obtain ⟨P2, B2⟩ := ly_perm_block hp2 k128
  rw [hB1] at P2 B2
  set Q := Fs.perm ⟨capOf P1, (lyCh σ 2).map (·, dsObserve)⟩ with hQ
  -- the first coordinate
  have e180 : σ (.n 178) = challengeOf Q := challengeT_value (s0 := .n 178) (b := 178) rfl (P2 0 (by omega))
  -- the second
  have hz : (([.n 25, .n 25, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28] ++ lyCap 178 : List V).map σ) =
      rateOf [] ++ capOf Q := by
    rw [ly_zero_rate c25 c26 c27 c28, B2]
  obtain ⟨k130, P3, B3⟩ := lyc_keccak (g 136 (.keccak ([.n 25, .n 25, .n 25, .n 25, .n 25, .n 26,
    .n 27, .n 28] ++ lyCap 178) (lyOuts 191) false false) (by decide +kernel))
  rw [hz] at P3 B3
  have e194 : σ (.n 191) = challengeOf (permOf (rateOf [] ++ capOf Q)) :=
    challengeT_value (s0 := .n 191) (b := 191) rfl (P3 0 (by omega))
  refine ⟨?_, e180, e194, ?_⟩
  · refine holdsList_straightN _ (by decide +kernel) ?_ trivial
    simp only [lyR5, List.forall_mem_cons, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true, keccakA]
    exact ⟨l150, m151, m152, m153, c154, m155, a156, m157, m158, m159, m160, a161, m162, m163,
      m164, m165, a166, show σ (.n 161) + σ (.n 177) = 0 by rw [e150, hcheck, ← e166, e_add_self],
      k128, k130⟩
  · rw [← B3]
    simp [lyCap]

/-- A tree's new value on its equations: its four children's multilinear value at the two new
coordinates, stored at `off`. -/
theorem lyc_val (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {t b off : ℕ} (n : ℕ)
    (heq : tbStmtsEqb (lyValT t b off) ((lyPre.drop n).take (lyValT t b off).length) = true)
    (ht : t < 3) (hb : 191 < b)
    (hl : LoadHolds rd (σ (.n 17)) off (multilinearEval (lyCh σ t) [σ (.n 178), σ (.n 191)]))
    (cp : ∀ i < 12, σ (.n (lyEv i + 3)) = σ (.n (lyEv i))) :
    ∀ s ∈ lyValT t b off, SHolds C rd σ s := by
  have gb := good_slice hG n (lyValT t b off) heq (by simp [lyValT, chValT, notIteB])
  have he : ∀ i < 4, lyEv (4 * t + i) + 3 < b := by
    intro i hi; unfold lyEv chB; omega
  have a0 : σ (.n b) = σ (.n (lyEv (4 * t + 0) + 3)) + σ (.n (lyEv (4 * t + 1) + 3)) :=
    gb (.atom (.add (.n b) _ _)) (by simp [lyValT, chValT])
  have m1 := good_mulS (gb (.atom (.mul (.n (b + 1)) (.n 178) (.n b))) (by simp [lyValT, chValT]))
    (by omega) (by omega)
  have a2 : σ (.n (b + 2)) = σ (.n (lyEv (4 * t + 0) + 3)) + σ (.n (b + 1)) :=
    gb (.atom (.add (.n (b + 2)) _ _)) (by simp [lyValT, chValT])
  have a3 : σ (.n (b + 3)) = σ (.n (lyEv (4 * t + 2) + 3)) + σ (.n (lyEv (4 * t + 3) + 3)) :=
    gb (.atom (.add (.n (b + 3)) _ _)) (by simp [lyValT, chValT])
  have m4 := good_mulS (gb (.atom (.mul (.n (b + 4)) (.n 178) (.n (b + 3))))
    (by simp [lyValT, chValT])) (by omega) (by omega)
  have a5 : σ (.n (b + 5)) = σ (.n (lyEv (4 * t + 2) + 3)) + σ (.n (b + 4)) :=
    gb (.atom (.add (.n (b + 5)) _ _)) (by simp [lyValT, chValT])
  have a6 : σ (.n (b + 6)) = σ (.n (b + 2)) + σ (.n (b + 5)) :=
    gb (.atom (.add (.n (b + 6)) _ _)) (by simp [lyValT, chValT])
  have m7 := good_mulS (gb (.atom (.mul (.n (b + 7)) (.n 191) (.n (b + 6))))
    (by simp [lyValT, chValT])) (by omega) (by omega)
  have a8 : σ (.n (b + 8)) = σ (.n (b + 2)) + σ (.n (b + 7)) :=
    gb (.atom (.add (.n (b + 8)) _ _)) (by simp [lyValT, chValT])
  have e8 : σ (.n (b + 8)) = multilinearEval (lyCh σ t) [σ (.n 178), σ (.n 191)] := by
    rw [a8, m7, a6, a5, m4, a3, a2, m1, a0, cp (4 * t + 0) (by omega), cp (4 * t + 1) (by omega),
      cp (4 * t + 2) (by omega), cp (4 * t + 3) (by omega), lyCh_eq]
    simp only [multilinearEval, List.foldl, foldPairs, List.headD]
    ring_nf
  simp only [lyValT, chValT, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  exact ⟨a0, m1, a2, a3, m4, a5, a6, m7, a8, show LoadHolds rd (σ (.n 17)) off (σ (.n (b + 8))) by
    rw [e8]; exact hl⟩

/-- **The next layer record and the next iteration**: the stores of the record `13` words on, and
the call at `x·g` below the bound. -/
theorem lyc_stores (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s)
    (cp : ∀ i < 12, σ (.n (lyEv i + 3)) = σ (.n (lyEv i)))
    (s40 : LoadHolds rd (σ (.n 45)) 40 (σ (.n 178)))
    (s41 : LoadHolds rd (σ (.n 45)) 41 (σ (.n 191)))
    (s26 : ∀ k < 5, LoadHolds rd (σ (.n 17)) (13 + k) (σ (.n (199 + k))))
    (s31 : LoadHolds rd (σ (.n 17)) 18 (σ (.n 86) * gen ^ 12))
    (sv : ∀ t < 3, LoadHolds rd (σ (.n 17)) (19 + t)
      (multilinearEval (lyCh σ t) [σ (.n 178), σ (.n 191)]))
    (s35 : LoadHolds rd (σ (.n 17)) 22 (σ (.n 45) * gen ^ 40))
    (s36 : LoadHolds rd (σ (.n 17)) 23 (σ (.n 46) * σ (.n 79) * gen ^ 7))
    {hv pv : E} (k4 : LoadHolds rd (σ (.n 9) * σ (.n 53)) 4 hv)
    (k0 : LoadHolds rd (σ (.n 9) * σ (.n 53)) 0 pv)
    (s37 : LoadHolds rd (σ (.n 17)) 24 (σ (.n 52) * hv))
    (s38 : LoadHolds rd (σ (.n 17)) 25 pv)
    (hK : IsInK (σ (.n 0) * gen + σ (.n 1)))
    (hcall : σ (.n 0) * gen + σ (.n 1) ≠ 0 →
      C name% «verify_bus_gkr_loop0» [σ (.n 0) * gen, σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4),
          σ (.n 5), σ (.n 6),
        σ (.n 7), σ (.n 8), σ (.n 9)] []) :
    Stmt.HoldsList C rd σ lyR6 True kret := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  have c195 : σ (.n 204) = word 4096 0 := g 144 (.const (.n 204) (word 4096 0))
    (by decide +kernel)
  have m196 := good_mul (g 145 (.mul (.n 205) (.n 86) (.n 204)) (by decide +kernel)) (by omega)
    (by omega)
  have c224 : σ (.n 233) = word 1099511627776 0 :=
    g 177 (.const (.n 233) (word 1099511627776 0)) (by decide +kernel)
  have m225 := good_mul (g 178 (.mul (.n 234) (.n 45) (.n 233)) (by decide +kernel)) (by omega)
    (by omega)
  have m226 := good_mul (g 180 (.mul (.n 235) (.n 46) (.n 79)) (by decide +kernel)) (by omega)
    (by omega)
  have c227 : σ (.n 236) = word 128 0 := g 181 (.const (.n 236) (word 128 0)) (by decide +kernel)
  have m228 := good_mul (g 182 (.mul (.n 237) (.n 235) (.n 236)) (by decide +kernel)) (by omega)
    (by omega)
  have m229 := good_mul (g 184 (.mul (.n 238) (.n 9) (.n 53)) (by decide +kernel)) (by omega)
    (by omega)
  obtain ⟨e230, l230⟩ := good_read (g 185 (.load (.n 239) (.n 238) 4) (by decide +kernel))
    (by decide +kernel) (by rw [m229]; exact k4)
  have m231 := good_mul (g 186 (.mul (.n 240) (.n 52) (.n 239)) (by decide +kernel)) (by omega)
    (by omega)
  have m232 := good_mul (g 188 (.mul (.n 241) (.n 9) (.n 53)) (by decide +kernel)) (by omega)
    (by omega)
  obtain ⟨e233, l233⟩ := good_read (g 189 (.load (.n 242) (.n 241) 0) (by decide +kernel))
    (by decide +kernel) (by rw [m232]; exact k0)
  have c234 : σ (.n 243) = word 2 0 := g 191 (.const (.n 243) (word 2 0)) (by decide +kernel)
  have m235 := good_mul (g 192 (.mul (.n 244) (.n 0) (.n 243)) (by decide +kernel)) (by omega)
    (by omega)
  have a236 : σ (.n 245) = σ (.n 244) + σ (.n 1) :=
    g 193 (.add (.n 245) (.n 244) (.n 1)) (by decide +kernel)
  have c237 : σ (.n 246) = word 2 0 := g 194 (.const (.n 246) (word 2 0)) (by decide +kernel)
  have m238 := good_mul (g 195 (.mul (.n 247) (.n 0) (.n 246)) (by decide +kernel)) (by omega)
    (by omega)
  have w4096 : word 4096 0 = gen ^ 12 := by
    rw [show (4096 : ℕ) = 2 ^ 12 by norm_num, tb_word_two_pow (by norm_num)]
  have w40 : word 1099511627776 0 = gen ^ 40 := by
    rw [show (1099511627776 : ℕ) = 2 ^ 40 by norm_num, tb_word_two_pow (by norm_num)]
  have w128 : word 128 0 = gen ^ 7 := by
    rw [show (128 : ℕ) = 2 ^ 7 by norm_num, tb_word_two_pow (by norm_num)]
  rw [tb_word_gen] at c234 c237
  refine holdsList_straightN _ (by decide +kernel) ?_ trivial
  simp only [lyR6, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
    List.mem_range, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, and_assoc]
  refine ⟨s40, s41, fun k hk => s26 k hk, c195, m196,
    show LoadHolds rd (σ (.n 17)) 18 (σ (.n 205)) by rw [m196, c195, w4096]; exact s31,
    lyc_val hG 147 (by decide +kernel) (by omega) (by omega) (sv 0 (by omega)) cp,
    lyc_val hG 157 (by decide +kernel) (by omega) (by omega) (sv 1 (by omega)) cp,
    lyc_val hG 167 (by decide +kernel) (by omega) (by omega) (sv 2 (by omega)) cp,
    c224, m225, show LoadHolds rd (σ (.n 17)) 22 (σ (.n 234)) by rw [m225, c224, w40]; exact s35,
    m226, c227, m228,
    show LoadHolds rd (σ (.n 17)) 23 (σ (.n 237)) by rw [m228, m226, c227, w128]; exact s36,
    m229, l230, m231, show LoadHolds rd (σ (.n 17)) 24 (σ (.n 240)) by rw [m231, e230]; exact s37,
    m232, l233, show LoadHolds rd (σ (.n 17)) 25 (σ (.n 242)) by rw [e233]; exact s38,
    show σ (.n 243) = word 2 0 by rw [c234, tb_word_gen], m235, a236,
    show σ (.n 246) = word 2 0 by rw [c237, tb_word_gen], m238,
    ⟨by rw [a236, m235, c234]; exact hK, fun hne => ?_⟩⟩
  show C name% «verify_bus_gkr_loop0» (List.map σ [.n 247, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6,
      .n 7, .n 8, .n 9]) []
  simp only [List.map_cons, List.map_nil]
  rw [m238, c237]
  exact hcall (by rw [a236, m235, c234] at hne; exact hne)

end Eval

end
end LeanVM.Guest.B1.Tables
