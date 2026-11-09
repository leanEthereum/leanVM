/-
  LeanVM.Guest.B1.Gkr.Parity

  The parity words `verify_bus_gkr`'s layer loop `__loop6` dispatches on are `g^e`, `e < 4`
  (`GkrPar`, the checker's obligation at the loop's cuts and at the loop's call).
-/

module

public import LeanVM.Guest.B1.Gkr.Holds
public import LeanVM.Guest.WalkTags

/-!
# The layer loop's parity (lean_ethereum.py:1799-1805, 1850, 1868-1934 at 40f877dc)

`__loop6`'s iteration `x` dispatches `gkr_rounds__L{2r}` on `parity = layer[g^12]`,
`layer = layers·(x²·depth_shift[g_bus_mu])^17` (`LAYER_SLOTS = 17`, `LAYER_PARITY = 12`).
The checker of the certificates bounds the dispatch's selector by the obligation `GkrPar` on the
loop's arguments `[layers, x, depth_shift, g_bus_mu, k_mod_next]` (`WalkTags.lean`): every
`k_mod_next[g^r]`, `r < 4`, and the parity word of layer `x`, if read, are `g^e`, `e < 4`.

* `ly_par_parity`: from the slot's statements on (`lyBody.take 62`, before the dispatch), the
  parity word the iteration reads (at `σ 16`, offset `12`) is such a power;
* `ly_par_tail`: before the tail call (`lyBody.take 297`), `GkrPar` holds at the tail call's
  `x·g` (`σ 346`): the iteration stores `layer(x·g)[g^12] = k_mod_next[parity]` (G:1934), the
  dispatch made `parity = g^r`, `r < 4`, and `layer(x·g) = layer(x)·g^34`;
* `vbg_par`: before `verify_bus_gkr`'s loop call (`vbgPre.take 224`), `GkrPar` at `x = 1`:
  `k_mod_next[g^r] = g^((r + 1) % 4)` (G:1801-1804), and the first layer's parity `g^0`, at
  `layers` for an even depth (G:1799), at `layers·g^17` for an odd one (G:1850),
  `depth_shift[g_bus_mu] = g^(depth % 2)`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `__loop6` -/

theorem lyBody_take62_noRet : Stmt.noRetList (lyBody.take 62) = true := by decide +kernel

theorem lyBody_take297_noRet : Stmt.noRetList (lyBody.take 297) = true := by decide +kernel

section Loop

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- The first ten statements of `__loop6`: the layer's slot `σ 16`. -/
def lySlotT : List Stmt :=
  [.atom (.mul (.n 7) (.n 0) (.n 0)), .atom (.mul (.n 8) (.n 2) (.n 3)),
    .atom (.load (.n 9) (.n 8) 0), .atom (.mul (.n 10) (.n 7) (.n 9)),
    .atom (.mul (.n 11) (.n 10) (.n 10)), .atom (.mul (.n 12) (.n 11) (.n 11)),
    .atom (.mul (.n 13) (.n 12) (.n 12)), .atom (.mul (.n 14) (.n 13) (.n 13)),
    .atom (.mul (.n 15) (.n 14) (.n 10)), .atom (.mul (.n 16) (.n 4) (.n 15))]

/-- The layer's slot at iteration `x`: `σ 16 = layers·(x·x·depth_shift[g_bus_mu])^17`, the depth
shift read at `σ 9`, over any return-free prefix starting with `lySlotT`. -/
theorem ly_slot {pre : List Stmt} (hnr : Stmt.noRetList pre = true)
    (h : Stmt.HoldsList C rd σ pre True kret)
    (heq : tbStmtsEqb lySlotT ((pre.drop 0).take lySlotT.length) = true) :
    LoadHolds rd (σ (.n 2) * σ (.n 3)) 0 (σ (.n 9)) ∧
      σ (.n 16) = σ (.n 4) * (σ (.n 0) * σ (.n 0) * σ (.n 9)) ^ 17 := by
  have hs := tb_holds_slice hnr h 0 lySlotT heq
  simp only [lySlotT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hs
  obtain ⟨m7, m8, l9, m10, m11, m12, m13, m14, m15, m16⟩ := hs
  rw [m8] at l9
  refine ⟨l9, ?_⟩
  rw [m16, m15, m14, m13, m12, m11, m10, m7]
  ring

/-- **The parity word** the iteration reads (`σ 16`, offset `12`) is `g^e`, `e < 4`, from
`GkrPar` on the loop's arguments, over any return-free prefix starting with `lySlotT` (before
the dispatch: `lyBody.take 62`). -/
theorem ly_par_parity {pre : List Stmt} (hnr : Stmt.noRetList pre = true)
    (h : Stmt.HoldsList C rd σ pre True kret)
    (heq : tbStmtsEqb lySlotT ((pre.drop 0).take lySlotT.length) = true)
    (hp : GkrPar rd (σ (.n 4)) (σ (.n 0)) (σ (.n 2)) (σ (.n 3)) (σ (.n 6))) :
    ∀ v, LoadHolds rd (σ (.n 16)) 12 v → ∃ e < 4, v = ofK (addressOfIndex e) := by
  obtain ⟨l9, e16⟩ := ly_slot hnr h heq
  intro v hv
  rw [e16] at hv
  exact hp.2 _ l9 v hv

/-- **`GkrPar` at the tail call's `x·g`** (`σ 346`), before the tail call: the next layer's
parity is the stored `k_mod_next[parity]`. -/
theorem ly_par_tail (h : Stmt.HoldsList C rd σ (lyBody.take 297) True kret)
    (hp : GkrPar rd (σ (.n 4)) (σ (.n 0)) (σ (.n 2)) (σ (.n 3)) (σ (.n 6))) :
    GkrPar rd (σ (.n 4)) (σ (.n 346)) (σ (.n 2)) (σ (.n 3)) (σ (.n 6)) := by
  have hnr := lyBody_take297_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  obtain ⟨l9, e16⟩ := ly_slot hnr h (by decide +kernel)
  obtain ⟨r, hr, e63, -⟩ := tb_holds_dispatch hnr h 62 (.n 63)
    ["gkr_rounds__L0", "gkr_rounds__L2", "gkr_rounds__L4", "gkr_rounds__L6"] [.n 70, .n 71] [.n 72]
    (by decide +kernel)
  have m340 := a 289 (.mul (.n 340) (.n 6) (.n 63)) (by decide +kernel)
  have l341 := a 290 (.load (.n 341) (.n 340) 0) (by decide +kernel)
  have s341 := a 291 (.load (.n 341) (.n 16) 46) (by decide +kernel)
  have c345 := a 295 (.const (.n 345) (word 2 0 0)) (by decide +kernel)
  have m346 := a 296 (.mul (.n 346) (.n 0) (.n 345)) (by decide +kernel)
  simp only [Atom.Holds] at m340 l341 s341 c345 m346
  have hr4 : r < 4 := by simpa using hr
  rw [m340, e63, ← gen_pow_eq_ofK, tb_loadHolds_mul_gen_pow, Nat.add_zero] at l341
  obtain ⟨e, he, e341⟩ := hp.1 r hr4 _ l341
  refine ⟨hp.1, fun s hs p hpl ↦ ⟨e, he, ?_⟩⟩
  rw [tb_loadHolds_unique hs l9, m346, c345, word_gen] at hpl
  have ea : σ (.n 4) * (σ (.n 0) * gen * (σ (.n 0) * gen) * σ (.n 9)) ^ 17 = σ (.n 16) * gen ^ 34 := by
    rw [e16]; ring
  rw [ea, tb_loadHolds_mul_gen_pow] at hpl
  rw [tb_loadHolds_unique hpl s341, e341]

end Loop

/-! ## `verify_bus_gkr`'s call of the loop -/

theorem vbgPre_take224_noRet : Stmt.noRetList (vbgPre.take 224) = true := by decide +kernel

/-- **`GkrPar` at the loop's call** (`x = 1`), before it (`vbgPre.take 224`), on a memory of at
most `2^32` words: the table `k_mod_next` and the first layer's parity `g^0`. -/
theorem vbg_par {C : CallRel} {σ : Val} {kret : List E → Prop} {μ : ℕ} (hμ : μ ≤ 32)
    (Lm : MemoryImage μ) (h : Stmt.HoldsList C Lm.read σ (vbgPre.take 224) True kret) :
    GkrPar Lm.read (σ (.n 15)) 1 (σ (.n 66)) (σ (.n 6)) (σ (.n 56)) := by
  have hnr := vbgPre_take224_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := Lm.read) (σ := σ) (kret := kret) hnr h n a heq
  -- the depth
  have c18 := a 10 (.const (.n 18) (word 4294967296 0 0)) (by decide +kernel)
  have rc := a 11 (.rangeCheck (.n 6) (.n 19) (.n 20) (.n 21) (.n 18)) (by decide +kernel)
  simp only [Atom.Holds] at c18 rc
  obtain ⟨depth, hd, hg⟩ := tb_rc_sound' hμ Lm (K := 33) (by omega) (by norm_num)
    (by rw [c18, show (4294967296 : ℕ) = 2 ^ 32 by norm_num, tb_word_two_pow (by norm_num),
      gen_pow_eq_ofK]) rc.1 rc.2.1 rc.2.2
  -- `k_mod_next`
  have hs := tb_holds_slice hnr h 62 ((List.range 4).map fun r ↦
    [Stmt.atom (.const (.n (57 + 2 * r)) (word (2 ^ ((r + 1) % 4)) 0 0)),
      .atom (.load (.n (57 + 2 * r)) (.n 56) r),
      .atom (.const (.n (58 + 2 * r)) (word (2 ^ ((r + 1) / 4)) 0 0)),
      .atom (.load (.n (58 + 2 * r)) (.n 56) (4 + r))]).flatten (by decide +kernel)
  rw [tb_holdsList_flatten_range _ _ (fun _ => rfl)] at hs
  refine ⟨fun r hr v hv ↦ ?_, fun s hs' p hpl ↦ ?_⟩
  · have := hs r hr
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
    obtain ⟨c0, l0, -, -⟩ := this
    rw [c0, tb_word_two_pow (by omega)] at l0
    exact ⟨(r + 1) % 4, Nat.mod_lt _ (by omega), by
      rw [tb_loadHolds_unique hv l0, gen_pow_eq_ofK]⟩
  -- `depth_shift[g_bus_mu] = g^(depth % 2)`
  have ht := tb_holds_slice hnr h 80 (((List.range 33).map fun k ↦
    [Stmt.atom (.const (.n (67 + 2 * k)) (word (2 ^ (k / 2)) 0 0)),
      .atom (.load (.n (67 + 2 * k)) (.n 65) k),
      .atom (.const (.n (68 + 2 * k)) (word (2 ^ (k % 2)) 0 0)),
      .atom (.load (.n (68 + 2 * k)) (.n 66) k)]).flatten) (by decide +kernel)
  rw [tb_holdsList_flatten_range _ _ (fun _ => rfl)] at ht
  have hk := ht depth hd
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hk
  obtain ⟨-, -, c1, l1⟩ := hk
  rw [c1, tb_word_two_pow (by omega)] at l1
  have hsh : LoadHolds Lm.read (σ (.n 66) * σ (.n 6)) 0 (gen ^ (depth % 2)) := by
    rw [hg, tb_loadHolds_mul_gen_pow]; exact l1
  rw [tb_loadHolds_unique hs' hsh, one_mul, one_mul, ← pow_mul] at hpl
  refine ⟨0, by omega, ?_⟩
  rw [← gen_pow_eq_ofK, pow_zero]
  rcases Nat.mod_two_eq_zero_or_one depth with h2 | h2
  · -- an even depth: the root slot's parity (G:1799)
    have c55 := a 59 (.const (.n 55) (word 1 0 0)) (by decide +kernel)
    have l55 := a 60 (.load (.n 55) (.n 15) 12) (by decide +kernel)
    simp only [Atom.Holds] at c55 l55
    rw [c55, tb_word_one] at l55
    rw [h2, Nat.zero_mul, pow_zero, mul_one] at hpl
    exact tb_loadHolds_unique hpl l55
  · -- an odd depth: the binary layer's slot (G:1850)
    have m133 := a 212 (.mul (.n 133) (.n 66) (.n 6)) (by decide +kernel)
    have l134 := a 213 (.load (.n 134) (.n 133) 0) (by decide +kernel)
    have c135 := a 214 (.const (.n 135) (word 1 0 0)) (by decide +kernel)
    have a136 := a 215 (.add (.n 136) (.n 134) (.n 135)) (by decide +kernel)
    simp only [Atom.Holds] at m133 l134 c135 a136
    rw [m133] at l134
    have e134 := tb_loadHolds_unique l134 hsh
    have hne : σ (.n 136) ≠ 0 := by
      rw [a136, e134, c135, tb_word_one, h2, pow_one]
      intro h0
      have h1 : gen ^ 1 = gen ^ 0 := by rw [pow_one, pow_zero]; exact e_add_eq_zero_iff.mp h0
      exact absurd (gen_pow_inj (by norm_num) (by norm_num) h1) (by norm_num)
    have hi := tb_holds_slice hnr h 216 [.ite (.n 136) [] odBody] (by decide +kernel)
    simp only [Stmt.HoldsList] at hi
    rw [tb_holds_ite_noRet _ _ _ (by decide) odBody_noRet] at hi
    have hod := hi.1.2.2 hne
    have c308 := tb_holds_atom odBody_noRet hod 149 (.const (.n 308) (word 1 0 0)) (by decide +kernel)
    have l308 := tb_holds_atom odBody_noRet hod 150 (.load (.n 308) (.n 15) 29) (by decide +kernel)
    simp only [Atom.Holds] at c308 l308
    rw [c308, tb_word_one] at l308
    rw [h2, Nat.one_mul, tb_loadHolds_mul_gen_pow] at hpl
    exact tb_loadHolds_unique hpl l308

end
end LeanVM.Guest.B1.Tables
