/-
  LeanVM.Guest.B1.Gkr.Parity

  The parity words `verify_bus_gkr`'s layer loop `verify_bus_gkr_loop0` dispatches on are `g^e`, `e
  < 4` (`GkrPar`, the checker's obligation at the loop's cuts and at the loop's call).
-/

module

public import LeanVM.Guest.B1.Gkr.Holds
public import LeanVM.Guest.WalkTags

/-!
# The layer loop's parity (lean_ethereum.py)

`verify_bus_gkr_loop0`'s iteration `x` dispatches `gkr_rounds__L{2r}` on `parity = layer[g^12]`,
`layer = layers·(x²·start_g)^13` (`LAYER_SLOTS = 13`, `LAYER_PARITY = 12`).
The checker of the certificates bounds the dispatch's selector by the obligation `GkrPar` on the
loop's arguments `[layers, x, start_g, k_mod_next]` (`WalkTags.lean`): every `k_mod_next[g^r]`,
`r < 4`, and the parity word of layer `x`, if read, are `g^e`, `e < 4`.

* `ly_par_parity`: from the slot's statements on (`lyBody.take 49`, before the dispatch), the
  parity word the iteration reads (at `σ 17`, offset `12`) is such a power;
* `ly_par_tail`: before the tail call (`lyBody.take 191`), `GkrPar` holds at the tail call's
  `x·g` (`σ 238`): the iteration stores `layer(x·g)[g^12] = k_mod_next[parity]`, the
  dispatch made `parity = g^r`, `r < 4`, and `layer(x·g) = layer(x)·g^26`;
* `vbg_par`: before `verify_bus_gkr`'s loop call (`vbgPre.take 206`), `GkrPar` at `x = 1`:
  `k_mod_next[g^r] = g^((r + 1) % 4)`, `start_g = g^(2 - depth % 2)`, and the first
  layer's parity, `g^0` at `layers·g^13` for an odd depth, `g` at `layers·g^26` for an
  even one.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `verify_bus_gkr_loop0` -/

theorem lyBody_take49_noRet : Stmt.noRetList (lyBody.take 49) = true := by decide +kernel

theorem lyBody_take191_noRet : Stmt.noRetList (lyBody.take 191) = true := by decide +kernel

section Loop

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- The first eight statements of `verify_bus_gkr_loop0`: the layer's slot `σ 17`. -/
def lySlotT : List Stmt :=
  [.atom (.mul (.n 10) (.n 0) (.n 0)), .atom (.mul (.n 11) (.n 10) (.n 2)),
    .atom (.mul (.n 12) (.n 11) (.n 11)), .atom (.mul (.n 13) (.n 12) (.n 11)),
    .atom (.mul (.n 14) (.n 13) (.n 13)), .atom (.mul (.n 15) (.n 14) (.n 14)),
    .atom (.mul (.n 16) (.n 15) (.n 11)), .atom (.mul (.n 17) (.n 3) (.n 16))]

/-- The layer's slot at iteration `x`: `σ 17 = layers·(x·x·start_g)^13`, over any return-free
prefix starting with `lySlotT`. -/
theorem ly_slot {pre : List Stmt} (hnr : Stmt.noRetList pre = true)
    (h : Stmt.HoldsList C rd σ pre True kret)
    (heq : tbStmtsEqb lySlotT ((pre.drop 0).take lySlotT.length) = true) :
    σ (.n 17) = σ (.n 3) * (σ (.n 0) * σ (.n 0) * σ (.n 2)) ^ 13 := by
  have hs := tb_holds_slice hnr h 0 lySlotT heq
  simp only [lySlotT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hs
  obtain ⟨m10, m11, m12, m13, m14, m15, m16, m17⟩ := hs
  rw [m17, m16, m15, m14, m13, m12, m11, m10]
  ring

/-- **The parity word** the iteration reads (`σ 17`, offset `12`) is `g^e`, `e < 4`, from
`GkrPar` on the loop's arguments, over any return-free prefix starting with `lySlotT` (before
the dispatch: `lyBody.take 49`). -/
theorem ly_par_parity {pre : List Stmt} (hnr : Stmt.noRetList pre = true)
    (h : Stmt.HoldsList C rd σ pre True kret)
    (heq : tbStmtsEqb lySlotT ((pre.drop 0).take lySlotT.length) = true)
    (hp : GkrPar rd (σ (.n 3)) (σ (.n 0)) (σ (.n 2)) (σ (.n 9))) :
    ∀ v, LoadHolds rd (σ (.n 17)) 12 v → ∃ e < 4, v = ofK (addressOfIndex e) := by
  rw [ly_slot hnr h heq]
  exact hp.2

/-- **`GkrPar` at the tail call's `x·g`** (`σ 238`), before the tail call: the next layer's
parity is the stored `k_mod_next[parity]`. -/
theorem ly_par_tail (h : Stmt.HoldsList C rd σ (lyBody.take 191) True kret)
    (hp : GkrPar rd (σ (.n 3)) (σ (.n 0)) (σ (.n 2)) (σ (.n 9))) :
    GkrPar rd (σ (.n 3)) (σ (.n 238)) (σ (.n 2)) (σ (.n 9)) := by
  have hnr := lyBody_take191_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have e17 := ly_slot hnr h (by decide +kernel)
  obtain ⟨r, hr, e54, -⟩ := tb_holds_dispatch hnr h 49 (.n 54)
    ["gkr_rounds__L0", "gkr_rounds__L2", "gkr_rounds__L4", "gkr_rounds__L6"] [.n 61, .n 62, .n 4]
    [.n 63] (by decide +kernel)
  have m232 := a 183 (.mul (.n 232) (.n 9) (.n 54)) (by decide +kernel)
  have l233 := a 184 (.load (.n 233) (.n 232) 0) (by decide +kernel)
  have s233 := a 185 (.load (.n 233) (.n 17) 38) (by decide +kernel)
  have c237 := a 189 (.const (.n 237) (word 2 0)) (by decide +kernel)
  have m238 := a 190 (.mul (.n 238) (.n 0) (.n 237)) (by decide +kernel)
  simp only [Atom.Holds] at m232 l233 s233 c237 m238
  have hr4 : r < 4 := by simpa using hr
  rw [m232, e54, ← gen_pow_eq_ofK, tb_loadHolds_mul_gen_pow, Nat.add_zero] at l233
  obtain ⟨e, he, e233⟩ := hp.1 r hr4 _ l233
  refine ⟨hp.1, fun p hpl ↦ ⟨e, he, ?_⟩⟩
  rw [m238, c237, tb_word_gen] at hpl
  have ea : σ (.n 3) * (σ (.n 0) * gen * (σ (.n 0) * gen) * σ (.n 2)) ^ 13 =
      σ (.n 17) * gen ^ 26 := by
    rw [e17]; ring
  rw [ea, tb_loadHolds_mul_gen_pow] at hpl
  rw [tb_loadHolds_unique hpl s233, e233]

end Loop

/-! ## `verify_bus_gkr`'s call of the loop -/

theorem vbgPre_take206_noRet : Stmt.noRetList (vbgPre.take 206) = true := by decide +kernel

/-- **`GkrPar` at the loop's call** (`x = 1`), before it (`vbgPre.take 206`), on a memory of at
most `2^32` words: the table `k_mod_next` and the first layer's parity. -/
theorem vbg_par {C : CallRel} {σ : Val} {kret : List E → Prop} {μ : ℕ} (hμ : μ ≤ 32)
    (Lm : MemoryImage μ) (h : Stmt.HoldsList C Lm.read σ (vbgPre.take 206) True kret) :
    GkrPar Lm.read (σ (.n 16)) 1 (σ (.n 375)) (σ (.n 64)) := by
  have hnr := vbgPre_take206_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := Lm.read) (σ := σ) (kret := kret) hnr h n a heq
  -- the depth
  have c19 := a 10 (.const (.n 19) (word 4294967296 0)) (by decide +kernel)
  have rc := a 11 (.rangeCheck (.n 6) (.n 20) (.n 21) (.n 22) (.n 19)) (by decide +kernel)
  simp only [Atom.Holds] at c19 rc
  obtain ⟨depth, hd, hg⟩ := tb_rc_sound' hμ Lm (K := 33) (by omega) (by norm_num)
    (by rw [c19, show (4294967296 : ℕ) = 2 ^ 32 by norm_num, tb_word_two_pow (by norm_num),
      gen_pow_eq_ofK]) rc.1 rc.2.1 rc.2.2
  -- `k_mod_next`
  have hk := tb_holds_slice hnr h 42 ((List.range 4).map fun r ↦
    [Stmt.atom (.const (.n (65 + 2 * r)) (word (2 ^ ((r + 1) % 4)) 0)),
      .atom (.load (.n (65 + 2 * r)) (.n 64) r),
      .atom (.const (.n (66 + 2 * r)) (word (2 ^ ((r + 1) / 4)) 0)),
      .atom (.load (.n (66 + 2 * r)) (.n 64) (4 + r))]).flatten (by decide +kernel)
  rw [tb_holdsList_flatten_range _ _ (fun _ => rfl)] at hk
  refine ⟨fun r hr v hv ↦ ?_, fun p hpl ↦ ?_⟩
  · have := hk r hr
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
    obtain ⟨c0, l0, -, -⟩ := this
    rw [c0, tb_word_two_pow (by omega)] at l0
    exact ⟨(r + 1) % 4, Nat.mod_lt _ (by omega), by
      rw [tb_loadHolds_unique hv l0, gen_pow_eq_ofK]⟩
  -- `odd_g = depth_odd[g_bus_mu] = g^(depth % 2)` and `start_g = g^(2 - depth % 2)`
  have ht := tb_holds_slice hnr h 60 (((List.range 33).map fun d ↦
    [Stmt.atom (.const (.n (75 + 2 * d)) (word (2 ^ ((d - 1) / 2)) 0)),
      .atom (.load (.n (75 + 2 * d)) (.n 73) d),
      .atom (.const (.n (76 + 2 * d)) (word (2 ^ (d % 2)) 0)),
      .atom (.load (.n (76 + 2 * d)) (.n 74) d)]).flatten) (by decide +kernel)
  rw [tb_holdsList_flatten_range _ _ (fun _ => rfl)] at ht
  have hdt := ht depth hd
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hdt
  obtain ⟨-, -, c1, l1⟩ := hdt
  rw [c1, tb_word_two_pow (by omega)] at l1
  have m141 := a 192 (.mul (.n 141) (.n 74) (.n 6)) (by decide +kernel)
  have l142 := a 193 (.load (.n 142) (.n 141) 0) (by decide +kernel)
  have c143 := a 194 (.const (.n 143) (word 1 0)) (by decide +kernel)
  have a144 := a 195 (.add (.n 144) (.n 142) (.n 143)) (by decide +kernel)
  have c374 := a 197 (.const (.n 374) (word 4 0)) (by decide +kernel)
  have m374 := a 198 (.mul (.n 374) (.n 375) (.n 142)) (by decide +kernel)
  simp only [Atom.Holds, tb_word_one] at m141 l142 c143 a144 c374 m374
  rw [m141, hg, tb_loadHolds_mul_gen_pow, Nat.add_zero] at l142
  have e142 := tb_loadHolds_unique l142 l1
  have e375 : σ (.n 375) = gen ^ (2 - depth % 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, tb_word_two_pow (by norm_num)] at c374
    rw [c374, e142] at m374
    apply mul_right_cancel₀ (pow_ne_zero (depth % 2) gen_ne_zero)
    rw [← m374, ← pow_add, Nat.sub_add_cancel (by omega)]
  rw [e375, one_mul, one_mul, ← pow_mul, tb_loadHolds_mul_gen_pow] at hpl
  have hi := tb_holds_slice hnr h 196 [.ite (.n 144) rtFour rtTwo] (by decide +kernel)
  simp only [Stmt.HoldsList] at hi
  rw [tb_holds_ite_noRet _ _ _ rtFour_noRet rtTwo_noRet] at hi
  obtain ⟨⟨-, hfour, htwo⟩, -⟩ := hi
  rcases Nat.mod_two_eq_zero_or_one depth with h2 | h2
  · -- an even depth: the radix-four root layer's slot, parity `g`
    have h0 : σ (.n 144) = 0 := by rw [a144, c143, e142, h2, pow_zero, e_add_self]
    have hf := hfour h0
    have c296 := tb_holds_atom rtFour_noRet hf 118 (.const (.n 296) (word 2 0)) (by decide +kernel)
    have l296 := tb_holds_atom rtFour_noRet hf 119 (.load (.n 296) (.n 16) 38) (by decide +kernel)
    simp only [Atom.Holds] at c296 l296
    rw [c296, tb_word_gen] at l296
    rw [h2] at hpl
    exact ⟨1, by omega, by rw [tb_loadHolds_unique hpl l296, ← gen_pow_eq_ofK, pow_one]⟩
  · -- an odd depth: the binary root layer's slot, parity `g^0`
    have hne : σ (.n 144) ≠ 0 := by
      rw [a144, c143, e142, h2, pow_one]
      intro h0
      have h1 : gen ^ 1 = gen ^ 0 := by rw [pow_one, pow_zero]; exact e_add_eq_zero_iff.mp h0
      exact absurd (gen_pow_inj (by norm_num) (by norm_num) h1) (by norm_num)
    have hf := htwo hne
    have c373 := tb_holds_atom rtTwo_noRet hf 66 (.const (.n 373) (word 1 0)) (by decide +kernel)
    have l373 := tb_holds_atom rtTwo_noRet hf 67 (.load (.n 373) (.n 16) 25) (by decide +kernel)
    simp only [Atom.Holds] at c373 l373
    rw [c373, tb_word_one] at l373
    rw [h2] at hpl
    exact ⟨0, by omega, by rw [tb_loadHolds_unique hpl l373, ← gen_pow_eq_ofK, pow_zero]⟩

end
end LeanVM.Guest.B1.Tables
