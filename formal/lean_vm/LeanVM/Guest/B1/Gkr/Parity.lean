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
`layer = layers·x^13` (a layer record of `LAYER_SLOTS = 13` words per radix-four layer,
`LAYER_PARITY = 12`). The guest's precondition bounds the dispatch's selector by the obligation
`GkrPar` on the loop's arguments `[layers, x, k_mod_next]` (`WalkTags.lean`): every
`k_mod_next[g^r]`, `r < 4`, and the parity word of layer `x`, if read, are `g^e`, `e < 4`.

* `ly_par_parity`: from the record's statements on (`lyBody.take 52`, before the dispatch), the
  parity word the iteration reads (at `σ 17`, offset `12`) is such a power;
* `ly_par_tail`: before the tail call (`lyBody.take 196`), `GkrPar` holds at the tail call's
  `x·g` (`σ 247`): the iteration stores `layer(x·g)[g^12] = k_mod_next[parity]`, the
  dispatch made `parity = g^r`, `r < 4`, and `layer(x·g) = layer(x)·g^13`;
* `vbg_par`: before `verify_bus_gkr`'s loop call (`vbgPre.take 280`), `GkrPar` at `x = 1`:
  `k_mod_next[g^r] = g^((r + 1) % 4)`, and the first layer record's parity, at `layers·g^12`:
  `g^0` for an odd depth, `g` for an even one.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `verify_bus_gkr_loop0` -/

theorem lyBody_take52_noRet : Stmt.noRetList (lyBody.take 52) = true := by decide +kernel

theorem lyBody_take196_noRet : Stmt.noRetList (lyBody.take 196) = true := by decide +kernel

section Loop

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- The first eight statements of `verify_bus_gkr_loop0`: the layer record `σ 17`. -/
def lySlotT : List Stmt :=
  [.atom (.mul (.n 10) (.n 0) (.n 0)), .atom (.mul (.n 11) (.n 10) (.n 2)),
    .atom (.mul (.n 12) (.n 0) (.n 0)), .atom (.mul (.n 13) (.n 12) (.n 0)),
    .atom (.mul (.n 14) (.n 13) (.n 13)), .atom (.mul (.n 15) (.n 14) (.n 14)),
    .atom (.mul (.n 16) (.n 15) (.n 0)), .atom (.mul (.n 17) (.n 3) (.n 16))]

/-- The layer record at iteration `x`: `σ 17 = layers·x^13`, over any return-free prefix starting
with `lySlotT`. -/
theorem ly_slot {pre : List Stmt} (hnr : Stmt.noRetList pre = true)
    (h : Stmt.HoldsList C rd σ pre True kret)
    (heq : tbStmtsEqb lySlotT ((pre.drop 0).take lySlotT.length) = true) :
    σ (.n 17) = σ (.n 3) * σ (.n 0) ^ 13 := by
  have hs := tb_holds_slice hnr h 0 lySlotT heq
  simp only [lySlotT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hs
  obtain ⟨-, -, m12, m13, m14, m15, m16, m17⟩ := hs
  rw [m17, m16, m15, m14, m13, m12]
  ring

/-- **The parity word** the iteration reads (`σ 17`, offset `12`) is `g^e`, `e < 4`, from
`GkrPar` on the loop's arguments, over any return-free prefix starting with `lySlotT` (before
the dispatch: `lyBody.take 52`). -/
theorem ly_par_parity {pre : List Stmt} (hnr : Stmt.noRetList pre = true)
    (h : Stmt.HoldsList C rd σ pre True kret)
    (heq : tbStmtsEqb lySlotT ((pre.drop 0).take lySlotT.length) = true)
    (hp : GkrPar rd (σ (.n 3)) (σ (.n 0)) (σ (.n 9))) :
    ∀ v, LoadHolds rd (σ (.n 17)) 12 v → ∃ e < 4, v = ofK (addressOfIndex e) := by
  rw [ly_slot hnr h heq]
  exact hp.2

/-- **`GkrPar` at the tail call's `x·g`** (`σ 247`), before the tail call: the next layer's
parity is the stored `k_mod_next[parity]`. -/
theorem ly_par_tail (h : Stmt.HoldsList C rd σ (lyBody.take 196) True kret)
    (hp : GkrPar rd (σ (.n 3)) (σ (.n 0)) (σ (.n 9))) :
    GkrPar rd (σ (.n 3)) (σ (.n 247)) (σ (.n 9)) := by
  have hnr := lyBody_take196_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have e17 := ly_slot hnr h (by decide +kernel)
  obtain ⟨r, hr, e54, -⟩ := tb_holds_dispatch hnr h 52 (.n 53)
    ["gkr_rounds__L0", "gkr_rounds__L2", "gkr_rounds__L4", "gkr_rounds__L6"] [.n 64, .n 65, .n 4]
    [.n 66] (by decide +kernel)
  have m241 := a 188 (.mul (.n 241) (.n 9) (.n 53)) (by decide +kernel)
  have l242 := a 189 (.load (.n 242) (.n 241) 0) (by decide +kernel)
  have s242 := a 190 (.load (.n 242) (.n 17) 25) (by decide +kernel)
  have c246 := a 194 (.const (.n 246) (word 2 0)) (by decide +kernel)
  have m247 := a 195 (.mul (.n 247) (.n 0) (.n 246)) (by decide +kernel)
  simp only [Atom.Holds] at m241 l242 s242 c246 m247
  have hr4 : r < 4 := by simpa using hr
  rw [m241, e54, ← gen_pow_eq_ofK, tb_loadHolds_mul_gen_pow, Nat.add_zero] at l242
  obtain ⟨e, he, e242⟩ := hp.1 r hr4 _ l242
  refine ⟨hp.1, fun p hpl ↦ ⟨e, he, ?_⟩⟩
  rw [m247, c246, tb_word_gen] at hpl
  have ea : σ (.n 3) * (σ (.n 0) * gen) ^ 13 = σ (.n 17) * gen ^ 13 := by
    rw [e17]; ring
  rw [ea, tb_loadHolds_mul_gen_pow] at hpl
  rw [tb_loadHolds_unique hpl s242, e242]

end Loop

/-! ## `verify_bus_gkr`'s call of the loop -/

theorem vbgPre_take280_noRet : Stmt.noRetList (vbgPre.take 280) = true := by decide +kernel

/-- **`GkrPar` at the loop's call** (`x = 1`), before it (`vbgPre.take 280`), on a memory of at
most `2^32` words: the table `k_mod_next` and the first layer record's parity. -/
theorem vbg_par {C : CallRel} {σ : Val} {kret : List E → Prop} {μ : ℕ} (hμ : μ ≤ 32)
    (Lm : MemoryImage μ) (h : Stmt.HoldsList C Lm.read σ (vbgPre.take 280) True kret) :
    GkrPar Lm.read (σ (.n 173)) 1 (σ (.n 53)) := by
  have hnr := vbgPre_take280_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := Lm.read) (σ := σ) (kret := kret) hnr h n a heq
  -- the depth
  have c9 := a 0 (.const (.n 9) (word 4294967296 0)) (by decide +kernel)
  have rc := a 1 (.rangeCheck (.n 6) (.n 10) (.n 11) (.n 12) (.n 9)) (by decide +kernel)
  simp only [Atom.Holds] at c9 rc
  obtain ⟨depth, hd, hg⟩ := tb_rc_sound' hμ Lm (K := 33) (by omega) (by norm_num)
    (by rw [c9, show (4294967296 : ℕ) = 2 ^ 32 by norm_num, tb_word_two_pow (by norm_num),
      gen_pow_eq_ofK]) rc.1 rc.2.1 rc.2.2
  -- `k_mod_next`
  have hk := tb_holds_slice hnr h 31 ((List.range 4).map fun r ↦
    [Stmt.atom (.const (.n (54 + 2 * r)) (word (2 ^ ((r + 1) % 4)) 0)),
      .atom (.load (.n (54 + 2 * r)) (.n 53) r),
      .atom (.const (.n (55 + 2 * r)) (word (2 ^ ((r + 1) / 4)) 0)),
      .atom (.load (.n (55 + 2 * r)) (.n 53) (4 + r))]).flatten (by decide +kernel)
  rw [tb_holdsList_flatten_range _ _ (fun _ => rfl)] at hk
  refine ⟨fun r hr v hv ↦ ?_, fun p hpl ↦ ?_⟩
  · have := hk r hr
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
    obtain ⟨c0, l0, -, -⟩ := this
    rw [c0, tb_word_two_pow (by omega)] at l0
    exact ⟨(r + 1) % 4, Nat.mod_lt _ (by omega), by
      rw [tb_loadHolds_unique hv l0, gen_pow_eq_ofK]⟩
  -- `odd_g = depth_odd[g_bus_mu] = g^(depth % 2)`
  have ht := tb_holds_slice hnr h 49 (((List.range 33).map fun d ↦
    [Stmt.atom (.const (.n (64 + 2 * d)) (word (2 ^ ((d - 1) / 2)) 0)),
      .atom (.load (.n (64 + 2 * d)) (.n 62) d),
      .atom (.const (.n (65 + 2 * d)) (word (2 ^ (d % 2)) 0)),
      .atom (.load (.n (65 + 2 * d)) (.n 63) d)]).flatten) (by decide +kernel)
  rw [tb_holdsList_flatten_range _ _ (fun _ => rfl)] at ht
  have hdt := ht depth hd
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hdt
  obtain ⟨-, -, c1, l1⟩ := hdt
  rw [c1, tb_word_two_pow (by omega)] at l1
  have m186 := a 270 (.mul (.n 186) (.n 63) (.n 6)) (by decide +kernel)
  have l187 := a 271 (.load (.n 187) (.n 186) 0) (by decide +kernel)
  have c188 := a 272 (.const (.n 188) (word 1 0)) (by decide +kernel)
  have a189 := a 273 (.add (.n 189) (.n 187) (.n 188)) (by decide +kernel)
  simp only [Atom.Holds, tb_word_one] at m186 l187 c188 a189
  rw [m186, hg, tb_loadHolds_mul_gen_pow, Nat.add_zero] at l187
  have e187 := tb_loadHolds_unique l187 l1
  rw [one_pow, mul_one] at hpl
  have hi := tb_holds_slice hnr h 274 [.ite (.n 189) rtFour rtTwo] (by decide +kernel)
  simp only [Stmt.HoldsList] at hi
  rw [tb_holds_ite_noRet _ _ _ rtFour_noRet rtTwo_noRet] at hi
  obtain ⟨⟨-, hfour, htwo⟩, -⟩ := hi
  rcases Nat.mod_two_eq_zero_or_one depth with h2 | h2
  · -- an even depth: the radix-four root layer's record, parity `g`
    have h0 : σ (.n 189) = 0 := by rw [a189, c188, e187, h2, pow_zero, e_add_self]
    have hf := hfour h0
    have c339 := tb_holds_atom rtFour_noRet hf 116 (.const (.n 339) (word 2 0)) (by decide +kernel)
    have l339 := tb_holds_atom rtFour_noRet hf 117 (.load (.n 339) (.n 173) 12) (by decide +kernel)
    simp only [Atom.Holds] at c339 l339
    rw [c339, tb_word_gen] at l339
    exact ⟨1, by omega, by rw [tb_loadHolds_unique hpl l339, ← gen_pow_eq_ofK, pow_one]⟩
  · -- an odd depth: the binary root layer's record, parity `g^0`
    have hne : σ (.n 189) ≠ 0 := by
      rw [a189, c188, e187, h2, pow_one]
      intro h0
      have h1 : gen ^ 1 = gen ^ 0 := by rw [pow_one, pow_zero]; exact e_add_eq_zero_iff.mp h0
      exact absurd (gen_pow_inj (by norm_num) (by norm_num) h1) (by norm_num)
    have hf := htwo hne
    have c415 := tb_holds_atom rtTwo_noRet hf 65 (.const (.n 415) (word 1 0)) (by decide +kernel)
    have l415 := tb_holds_atom rtTwo_noRet hf 66 (.load (.n 415) (.n 173) 12) (by decide +kernel)
    simp only [Atom.Holds] at c415 l415
    rw [c415, tb_word_one] at l415
    exact ⟨0, by omega, by rw [tb_loadHolds_unique hpl l415, ← gen_pow_eq_ofK, pow_zero]⟩

end
end LeanVM.Guest.B1.Tables
