/-
  LeanVM.Guest.B1.Digest.ClaimList

  B1 for `claim_list_digest` (G:2762-2799; TRIAGE #62) and its window loop `__loop86`: the
  BLAKE2s of a list of claims, 64 bytes a claim.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimSpec

/-!
# `claim_list_digest`

`claim_list_digest(entries_ptr, n_g, g_squares)`: for `n_g = g^n`, the BLAKE2s of the `4n` cells
at `entries_ptr`, in windows of 32 claims (`__loop86` over `claims_window`), a tail of fewer
than 32 (`claims_tail__L{t}`) and the last claim, absorbed apart with the total length and the
final flag. The windows chain through a scratch table of four cells a window (the state, the
window's base, its first entry).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-! ## `__loop86` -/

/-- `__loop86`'s body. -/
def l86Body : List Stmt :=
  ([.mul (.n 4) (.n 0) (.n 0), .mul (.n 5) (.n 4) (.n 4), .mul (.n 6) (.n 2) (.n 5),
    .load (.n 7) (.n 6) 0, .load (.n 8) (.n 6) 1, .load (.n 9) (.n 6) 2, .load (.n 10) (.n 6) 3] :
    List Atom).map .atom ++
  [.call "claims_window" [.n 7, .n 8, .n 9, .n 10, .n 0, .n 3] [.n 11, .n 12, .n 13]] ++
  ([.const (.n 14) (word 2 0 0), .mul (.n 15) (.n 0) (.n 14), .mul (.n 16) (.n 15) (.n 15),
    .mul (.n 17) (.n 16) (.n 16), .mul (.n 18) (.n 2) (.n 17), .load (.n 11) (.n 18) 0,
    .load (.n 12) (.n 18) 1, .load (.n 13) (.n 18) 2, .load (.n 19) (.n 6) 3,
    .const (.n 20) (word 325 0 0), .mul (.n 21) (.n 19) (.n 20), .load (.n 21) (.n 18) 3,
    .const (.n 22) (word 2 0 0), .mul (.n 23) (.n 0) (.n 22), .add (.n 24) (.n 23) (.n 1),
    .const (.n 25) (word 2 0 0), .mul (.n 26) (.n 0) (.n 25)] : List Atom).map .atom ++
  [.callIf (.n 24) "__loop86" [.n 26, .n 1, .n 2, .n 3], .ret []]

set_option maxRecDepth 100000 in
theorem find_loop86 : coreProgram.find? "__loop86" =
    some ⟨"__loop86", [.n 0, .n 1, .n 2, .n 3], l86Body⟩ :=
  Program.find?_of_indexOf? (j := 462) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem word_g128 : word 325 0 0 = gen ^ 128 := by
  rw [word_eq_eOfNat, gen_pow_eq_ofK, eOfNat, ← gpowK_eq (by unfold u128Bound; omega)]
  congr 1

/-- One iteration of `__loop86` at `x`: the window's slot read at `chain·x⁴`, the window run, its
results and next entry pointer stored at `chain·(x·g)⁴`. -/
def L86Step (rd : Reader) (chain gsq : E) (C : CallRel) (x : E) : Prop :=
  ∃ s0 s1 base ptr o0 o1 nxt, CellsAt rd (chain * (x * x * (x * x))) [s0, s1, base, ptr] ∧
    C "claims_window" [s0, s1, base, ptr, x, gsq] [o0, o1, nxt] ∧
    CellsAt rd (chain * (x * gen * (x * gen) * (x * gen * (x * gen)))) [o0, o1, nxt, ptr * word 325 0 0]

theorem l86_step (rd : Reader) (W c gsq : E) (C : CallRel) (x : E) :
    (∃ fn, coreProgram.find? "__loop86" = some fn ∧ fn.Sem C rd (x :: [W, c, gsq]) []) ↔
      L86Step rd c gsq C x ∧ IsInK (x * gen + W) ∧
        (x * gen + W ≠ 0 → C "__loop86" (x * gen :: [W, c, gsq]) []) := by
  have hf : ∀ fn, coreProgram.find? "__loop86" = some fn ↔
      fn = ⟨"__loop86", [.n 0, .n 1, .n 2, .n 3], l86Body⟩ := fun fn => by
    rw [find_loop86]; exact ⟨fun h => (Option.some.inj h).symm, fun h => by rw [h]⟩
  simp only [hf, exists_eq_left]
  simp only [Fn.Sem, l86Body, List.cons_append, List.nil_append, Stmt.HoldsList,
    Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, L86Step, cellsAt_four, ← word_gen]
  constructor
  · rintro ⟨σ, hp, m4, m5, m6, l7, l8, l9, l10, hcall, c14, m15, m16, m17, m18, l11, l12, l13,
      l19, c20, m21, l21, c22, m23, a24, c25, m26, hk, hnext, -⟩
    simp only [List.cons.injEq, and_true] at hp
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hp
    rw [m6, m5, m4] at l7 l8 l9 l10 l19
    rw [m18, m17, m16, m15, c14] at l11 l12 l13 l21
    rw [loadHolds_unique l19 l10, c20] at m21
    rw [m21] at l21
    rw [a24, m23, c22] at hk hnext
    rw [m26, c25] at hnext
    exact ⟨⟨_, _, _, _, _, _, _, ⟨l7, l8, l9, l10⟩, hcall, ⟨l11, l12, l13, l21⟩⟩, hk, hnext⟩
  · rintro ⟨⟨s0, s1, base, ptr, o0, o1, nxt, ⟨l7, l8, l9, l10⟩, hcall, ⟨l11, l12, l13, l21⟩⟩, hk,
      hnext⟩
    refine ⟨listVal [x, W, c, gsq, x * x, x * x * (x * x), c * (x * x * (x * x)), s0, s1, base, ptr,
      o0, o1, nxt, word 2 0 0, x * word 2 0 0, x * word 2 0 0 * (x * word 2 0 0),
      x * word 2 0 0 * (x * word 2 0 0) * (x * word 2 0 0 * (x * word 2 0 0)),
      c * (x * word 2 0 0 * (x * word 2 0 0) * (x * word 2 0 0 * (x * word 2 0 0))), ptr,
      word 325 0 0, ptr * word 325 0 0, word 2 0 0, x * word 2 0 0, x * word 2 0 0 + W,
      word 2 0 0, x * word 2 0 0], rfl, ?_⟩
    simp only [listVal, List.getD_cons_succ, List.getD_cons_zero, true_and]
    exact ⟨l7, l8, l9, l10, hcall, l11, l12, l13, l10, l21, hk, hnext, trivial⟩

/-! ## `claim_list_digest` -/

/-- The scratch table of a claim list's windows: window `q ≤ w` at `chain·g^(4q)`, its state after
`32q` blocks, its base `E(2^11·q)` and its first entry `ptr·g^(128q)`. -/
def ClScratch (rd : Reader) (ptr chain : E) (cs : List E) (w : ℕ) : Prop :=
  ∀ q ≤ w, CellsAt rd (chain * gen ^ (4 * q)) [(digestScalars (prefixDigest cs (32 * q))).1,
    (digestScalars (prefixDigest cs (32 * q))).2, eOfNat (2 ^ 11 * q), ptr * gen ^ (128 * q)]

/-- **`claim_list_digest(ptr, n_g, g_squares)`**: `n_g = g^n`, `n < 2^16`, and the digest is the
BLAKE2s of the `4n` canonical cells at `ptr`; the windows' scratch table holds their states. -/
def Meaning_claim_list_digest (rd : Reader) (args rets : List E) : Prop :=
  ∃ ptr n_g gsq d0 d1, args = [ptr, n_g, gsq] ∧ rets = [d0, d1] ∧ ∃ n < 2 ^ 16, n_g = gen ^ n ∧
    ∃ cs : List E, cs.length = 4 * n ∧ CellsAt rd ptr cs ∧ (∀ c ∈ cs, IsCanonical128 c) ∧
      (d0, d1) = digestScalars (blake2sBytes (cs.flatMap cellBytes)) ∧
      (n = 0 ∨ ∃ chain, ClScratch rd ptr chain cs ((n - 1) / 32))

/-- `claim_list_digest`'s body. -/
def cldBody : List Stmt :=
  [.atom (.const (.n 3) (word 1 0 0)), .atom (.add (.n 4) (.n 1) (.n 3)),
   .ite (.n 4)
    (([.const (.n 5) (word 0 0 0), .const (.n 6) (word 0 0 0), .const (.n 7) (word 0 0 0),
      .const (.n 8) (word 0 0 0), .const (.n 9) (word 13503953895743350343 11912009169889063794 0),
      .const (.n 10) (word 11170449402626986623 6620516960021240235 0),
      .const (.n 11) (word 0 4294967295 0),
      .blake2s (.n 5) (.n 6) (.n 7) (.n 8) (.n 9) (.n 10) (.n 12) (.n 13) (.n 11)] : List Atom).map .atom)
    (([.hint (.witness "signers_split" (.stack [.n 14, .n 15])),
      .const (.n 16) (word 2147483648 0 0), .rangeCheck (.n 15) (.n 17) (.n 18) (.n 19) (.n 16),
      .const (.n 20) (word 55834575010 0 0), .rangeCheck (.n 14) (.n 21) (.n 22) (.n 23) (.n 20),
      .mul (.n 24) (.n 14) (.n 14), .mul (.n 25) (.n 24) (.n 24), .mul (.n 26) (.n 25) (.n 25),
      .mul (.n 27) (.n 26) (.n 26), .mul (.n 28) (.n 27) (.n 27), .mul (.n 29) (.n 28) (.n 15),
      .const (.n 30) (word 9223372036854775821 0 0), .mul (.n 31) (.n 1) (.n 30),
      .assertEq (.n 29) (.n 31), .const (.n 32) (word 2 0 0), .mul (.n 33) (.n 14) (.n 32),
      .mul (.n 34) (.n 33) (.n 33), .mul (.n 35) (.n 34) (.n 34), .hint (.allocDyn (.n 36) (.n 35)),
      .const (.n 37) (word 13503953895743350343 11912009169889063794 0), .load (.n 37) (.n 36) 0,
      .const (.n 38) (word 11170449402626986623 6620516960021240235 0), .load (.n 38) (.n 36) 1,
      .const (.n 39) (word 0 0 0), .load (.n 39) (.n 36) 2, .load (.n 0) (.n 36) 3,
      .const (.n 40) (word 1 0 0), .add (.n 41) (.n 40) (.n 14), .const (.n 42) (word 1 0 0)] :
      List Atom).map .atom ++
    [.callIf (.n 41) "__loop86" [.n 42, .n 14, .n 36, .n 2]] ++
    ([.mul (.n 43) (.n 14) (.n 14), .mul (.n 44) (.n 43) (.n 43), .mul (.n 45) (.n 36) (.n 44),
      .load (.n 46) (.n 45) 0, .load (.n 47) (.n 45) 1, .load (.n 48) (.n 45) 2,
      .load (.n 49) (.n 45) 3] : List Atom).map .atom ++
    [.dispatch (.n 15) ctNames [.n 46, .n 47, .n 48, .n 49] [.n 50, .n 51, .n 52]] ++
    ([.hint (.witness "claims" (.heap (.n 52) 0 4))] : List Atom).map .atom ++
    [.call "scaled_log__L6" [.n 1, .n 2] [.n 53]] ++
    ([.const (.n 54) (word 0 4294967295 0), .add (.n 55) (.n 53) (.n 54), .load (.n 56) (.n 52) 0,
      .load (.n 57) (.n 52) 1, .load (.n 58) (.n 52) 2, .load (.n 59) (.n 52) 3,
      .blake2s (.n 56) (.n 57) (.n 58) (.n 59) (.n 50) (.n 51) (.n 12) (.n 13) (.n 55)] :
      List Atom).map .atom),
   .atom (.copy (.n 60) (.n 12)), .atom (.copy (.n 61) (.n 13)), .ret [.n 60, .n 61]]

set_option maxRecDepth 100000 in
theorem find_claim_list_digest : coreProgram.find? "claim_list_digest" =
    some ⟨"claim_list_digest", [.n 0, .n 1, .n 2], cldBody⟩ :=
  Program.find?_of_indexOf? (j := 20) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem word_g2047 : word 55834575010 0 0 = gen ^ 2047 := by
  rw [word_eq_eOfNat, gen_pow_eq_ofK, eOfNat, ← gpowK_eq (by unfold u128Bound; omega)]
  congr 1

theorem word_g31 : word 2147483648 0 0 = gen ^ 31 := by
  rw [gen_pow_eq_eOfNat (by omega), word_eq_eOfNat]; rfl

theorem md_final_word : word 0 4294967295 0 = metadataCell 0 true := rfl

/-- What a window establishes of the scratch table: window `q`'s slot holds the state after
`32q` blocks, and window `q + 1`'s the state after `32(q + 1)`. -/
def WinInv (rd : Reader) (p c : E) (len q : ℕ) : Prop :=
  CellsAt rd (c * gen ^ (4 * q)) [(digestScalars (prefixDigest (cellsFrom rd p len) (32 * q))).1,
    (digestScalars (prefixDigest (cellsFrom rd p len) (32 * q))).2, eOfNat (2 ^ 11 * q),
    p * gen ^ (128 * q)] ∧
  (∀ j < 32 * q, ∀ r, IsCanonical128 (blocksOf (cellsFrom rd p len) j r)) ∧
  (∀ i < 128 * q, LoadHolds rd p i (cellAt rd p i))

/-- **The windows, forward**: from the initial slot, `w` loop iterations establish the scratch
table, the canonicity and the reads of the first `32w` blocks. -/
theorem windows_fwd {rd : Reader} {gsq p c : E} (hT : SquaresAt rd gsq) {len w : ℕ}
    (hw : 128 * w ≤ len) (hw' : w < 2 ^ 11)
    (h0 : CellsAt rd c [(digestScalars paramIv).1, (digestScalars paramIv).2, 0, p])
    (hstep : ∀ j < w, L86Step rd c gsq (coreProgram.Rel rd) (gen ^ j)) :
    ∀ q ≤ w, WinInv rd p c len q := by
  intro q hq
  induction q with
  | zero =>
    refine ⟨?_, fun j hj => absurd hj (by omega), fun i hi => absurd hi (by omega)⟩
    simpa [eOfNat_zero, prefixDigest, absorbBlocks] using h0
  | succ q ih =>
    obtain ⟨hI, hcan, hld⟩ := ih (by omega)
    obtain ⟨s0, s1, base, ptr, o0, o1, nxt, hslot, hwin, hstore⟩ := hstep q (by omega)
    rw [pow4_eq _ q rfl] at hslot
    rw [cellsAt_four] at hslot hI
    have e0 := loadHolds_unique hslot.1 hI.1
    have e1 := loadHolds_unique hslot.2.1 hI.2.1
    have e2 := loadHolds_unique hslot.2.2.1 hI.2.2.1
    have e3 := loadHolds_unique hslot.2.2.2 hI.2.2.2
    subst e0 e1 e2 e3
    obtain ⟨_, _, _, _, _, _, o0', o1', nxt', hargs, hrets, N, hN, hxq, hnxt, csq, hlen, hcells,
      hch⟩ := (claims_window_iff hT _ _ _ _ _ _).mp hwin
    simp only [List.cons.injEq, and_true] at hargs hrets
    obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := hargs
    obtain ⟨rfl, rfl, rfl⟩ := hrets
    rw [← pow_succ] at hxq
    have hNq : N = q + 1 := (gen_pow_inj' (by omega) (lt_trans hN (by norm_num)) hxq).symm
    subst hNq
    have hb := blocksOf_slice (len := len) (b := 32 * q) 32
      (by rw [show 4 * (32 * q) = 128 * q by ring]; exact hcells) hlen (by omega)
    rw [chainCells_prefix (k := 32 * q) hb (fun j hj => by rw [hnxt]; exact windowMd_eq q j hj)] at hch
    obtain ⟨hcan', hout⟩ := hch
    refine ⟨?_, fun j hj => ?_, fun i hi => ?_⟩
    · rw [show c * (gen ^ q * gen * (gen ^ q * gen) * (gen ^ q * gen * (gen ^ q * gen))) =
        c * gen ^ (4 * (q + 1)) by rw [← pow_succ, pow4_eq _ (q + 1) rfl]] at hstore
      rw [cellsAt_four] at hstore ⊢
      rw [show 32 * (q + 1) = 32 * q + 32 by ring, ← hout, ← hnxt,
        show p * gen ^ (128 * (q + 1)) = p * gen ^ (128 * q) * word 325 0 0 by
          rw [word_g128, mul_assoc, ← pow_add, show 128 * (q + 1) = 128 * q + 128 by ring]]
      exact hstore
    · rcases Nat.lt_or_ge j (32 * q) with h | h
      · exact hcan j h
      · have := hcan' (j - 32 * q) (by omega)
        rwa [show 32 * q + (j - 32 * q) = j by omega] at this
    · rcases Nat.lt_or_ge i (128 * q) with h | h
      · exact hld i h
      · have := loads_slice hcells (i - 128 * q) (by omega)
        rwa [show 128 * q + (i - 128 * q) = i by omega] at this

theorem l86Step_mono (rd : Reader) (c gsq : E) :
    ∀ C C' x, CallRel.Le C C' → L86Step rd c gsq C x → L86Step rd c gsq C' x :=
  fun _ _ _ hC ⟨a, b, d, e, f, g, h, h1, h2, h3⟩ => ⟨a, b, d, e, f, g, h, h1, hC _ _ _ h2, h3⟩

/-- **`__loop86`** from `g^k` to `W`: `W = g^m` for the first `m > k` the loop reaches, every
iteration `g^j`, `k ≤ j < m`, holding. -/
theorem loop86_iff (rd : Reader) (W c gsq : E) (k : ℕ) :
    coreProgram.Rel rd "__loop86" (gen ^ k :: [W, c, gsq]) [] ↔
      ∃ m, k < m ∧ W = gen ^ m ∧ (∀ j, k < j → j < m → gen ^ j ≠ W) ∧
        ∀ j, k ≤ j → j < m → L86Step rd c gsq (coreProgram.Rel rd) (gen ^ j) :=
  loop_iff (l86Step_mono rd c gsq) (l86_step rd W c gsq) k

/-- Canonical blocks make every cell canonical. -/
theorem canonical_of_blocks {cs : List E} {n : ℕ} (hlen : cs.length = 4 * n)
    (h : ∀ j < n, ∀ r, IsCanonical128 (blocksOf cs j r)) : ∀ c ∈ cs, IsCanonical128 c := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have := h (i / 4) (by omega) ⟨i % 4, by omega⟩
  have hr : ∀ (r : ℕ) (hr : r < 4), (blocksOf cs (i / 4) ⟨r, hr⟩ : E) = cs.getD (4 * (i / 4) + r) 0 := by
    intro r hr
    interval_cases r <;> rfl
  rw [hr (i % 4) (by omega), show 4 * (i / 4) + i % 4 = i by omega,
    List.getD_eq_getElem _ _ hi] at this
  exact this

/-- The loop's iterations, from the entry `callIf`: `w` of them, at `g^j`, `j < w`. -/
theorem loop86_iters {rd : Reader} {W c gsq : E} {w : ℕ} (hW : W = gen ^ w) (hw : w < 2 ^ 33)
    (h : coreProgram.Rel rd "__loop86" [gen ^ 0, W, c, gsq] []) :
    ∀ j < w, L86Step rd c gsq (coreProgram.Rel rd) (gen ^ j) := by
  intro j hj
  obtain ⟨m, hm0, hmN, hfirst, hall⟩ :=
    (loop_iff (l86Step_mono rd c gsq) (l86_step rd W c gsq) 0).mp h
  have hmw : m = w := by
    rcases Nat.lt_or_ge w m with hlt | hge
    · exact absurd hW.symm (hfirst w (by omega) hlt)
    · exact gen_pow_inj' (by omega) hw (hmN.symm.trans hW)
  exact hall j (by omega) (by omega)

/-- **The windows, backward**: canonical cells and a scratch table holding the states make every
loop iteration hold. -/
theorem windows_bwd {rd : Reader} {gsq p c : E} (hT : SquaresAt rd gsq) {cs : List E} {n w : ℕ}
    (hlen : cs.length = 4 * n) (hw : 32 * w ≤ n) (hn : n < 2 ^ 16) (hcells : CellsAt rd p cs)
    (hcan : ∀ x ∈ cs, IsCanonical128 x) (hscr : ClScratch rd p c cs w) :
    ∀ j < w, L86Step rd c gsq (coreProgram.Rel rd) (gen ^ j) := by
  intro j hj
  have h0 := hscr j (by omega)
  have h1 := hscr (j + 1) (by omega)
  rw [show 32 * (j + 1) = 32 * j + 32 by ring] at h1
  refine ⟨_, _, _, _, (digestScalars (prefixDigest cs (32 * j + 32))).1,
    (digestScalars (prefixDigest cs (32 * j + 32))).2, eOfNat (2 ^ 11 * (j + 1)),
    by rw [pow4_eq _ j rfl]; exact h0, ?_, ?_⟩
  · refine (claims_window_iff hT _ _ _ _ _ _).mpr ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, j + 1,
      by omega, (pow_succ gen j).symm, rfl, sliceOf cs (32 * j) 32, length_sliceOf _ _ _, ?_, ?_⟩
    · rw [show 128 * j = 4 * (32 * j) by ring]
      exact cellsAt_sliceOf hcells (by omega)
    · refine (chainCells_prefix (blocksOf_sliceOf cs (32 * j) 32)
        (fun i hi => windowMd_eq j i hi)).mpr ⟨fun i hi r => ?_, rfl⟩
      exact blocks_canonical hlen hcan _ (by omega) r
  · rw [← pow_succ, pow4_eq _ (j + 1) rfl,
      show p * gen ^ (128 * j) * word 325 0 0 = p * gen ^ (128 * (j + 1)) by
        rw [word_g128, mul_assoc, ← pow_add, show 128 * (j + 1) = 128 * j + 128 by ring]]
    exact h1

theorem compressCells_empty_iff {o0 o1 : E} :
    CompressCells ![0, 0, 0, 0] (digestScalars paramIv).1 (digestScalars paramIv).2 o0 o1
      (metadataCell 0 true) ↔ (o0, o1) = digestScalars (blake2sBytes []) := by
  refine ⟨blake2s_empty, fun h => ?_⟩
  have hc : CompressCells ![0, 0, 0, 0] (digestScalars paramIv).1 (digestScalars paramIv).2
      (digestScalars (chainRun paramIv (fun _ => ![0, 0, 0, 0]) (fun _ => metadataCell 0 true) 1)).1
      (digestScalars (chainRun paramIv (fun _ => ![0, 0, 0, 0]) (fun _ => metadataCell 0 true) 1)).2
      (metadataCell 0 true) :=
    (compressCells_chainRun (h := paramIv) (blocks := fun _ => ![0, 0, 0, 0])
      (md := fun _ => metadataCell 0 true) (i := 0)
      (fun r => by fin_cases r <;> exact isCanonical128_zero)
      (isCanonical128_metadataCell _ _)).mpr rfl
  have he := blake2s_empty hc
  rw [Prod.mk.eta] at he
  rw [he, ← h] at hc
  exact hc

/-- The honest values of `claim_list_digest`, `n ≥ 1`. -/
noncomputable def cldList (p gsq c d0 d1 : E) (cs : List E) (n w t : ℕ) (t1 t2 t3 t4 : E) : List E :=
  [p, gen ^ n, gsq, word 1 0 0, gen ^ n + word 1 0 0, 0, 0, 0, 0, 0, 0, 0, d0,
  d1, gen ^ w, gen ^ t, word 2147483648 0 0, gen ^ (31 - t), t1, t2, word 55834575010 0 0,
  gen ^ (2047 - w), t3, t4, gen ^ w * gen ^ w, gen ^ w * gen ^ w * (gen ^ w * gen ^ w),
  gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)),
  gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) *
    (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w))),
  gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) *
    (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w))) *
    (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) *
    (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)))),
  gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) *
    (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w))) *
    (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) *
    (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)))) *
    gen ^ t,
  word 9223372036854775821 0 0, gen ^ n * word 9223372036854775821 0 0, word 2 0 0,
  gen ^ w * word 2 0 0, gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0),
  gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0) * (gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0)),
  c, word 13503953895743350343 11912009169889063794 0,
  word 11170449402626986623 6620516960021240235 0, word 0 0 0, word 1 0 0,
  word 1 0 0 + gen ^ w, word 1 0 0, gen ^ w * gen ^ w, gen ^ w * gen ^ w * (gen ^ w * gen ^ w),
  c * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)),
  (digestScalars (prefixDigest cs (32 * w))).1, (digestScalars (prefixDigest cs (32 * w))).2,
  eOfNat (2 ^ 11 * w), p * gen ^ (128 * w), (digestScalars (prefixDigest cs (n - 1))).1,
  (digestScalars (prefixDigest cs (n - 1))).2, p * gen ^ (128 * w) * gen ^ (4 * t),
  eOfNat (2 ^ 6 * n), word 0 4294967295 0, eOfNat (2 ^ 6 * n) + word 0 4294967295 0,
  cs.getD (4 * (n - 1) + 0) 0, cs.getD (4 * (n - 1) + 1) 0, cs.getD (4 * (n - 1) + 2) 0,
  cs.getD (4 * (n - 1) + 3) 0, d0, d1]

/-- **`claim_list_digest`'s body holds**, `n ≥ 1`, at its honest values, on a memory defined below
`2^16` holding the squares table, the cells and the windows' scratch table at `c`. -/
theorem cld_holds_pos {rd : Reader} (hl : Low16 rd) {gsq : E} (hT : SquaresAt rd gsq) {p c : E} {n : ℕ}
    (hn : n < 2 ^ 16) (hn1 : 0 < n) {cs : List E} (hlen : cs.length = 4 * n) (hcells : CellsAt rd p cs)
    (hcan : ∀ x ∈ cs, IsCanonical128 x) (hscr : ClScratch rd p c cs ((n - 1) / 32)) {d0 d1 : E}
    (hd : (d0, d1) = digestScalars (blake2sBytes (cs.flatMap cellBytes))) :
    ∃ t1 t2 t3 t4, Stmt.HoldsList (coreProgram.Rel rd) rd
      (listVal (cldList p gsq c d0 d1 cs n ((n - 1) / 32) ((n - 1) % 32) t1 t2 t3 t4)) cldBody False
      (fun rs => rs = [d0, d1]) := by
  set w := (n - 1) / 32 with hw
  set t := (n - 1) % 32 with ht
  have hwt : n = 32 * w + t + 1 := by omega
  have ht32 : t < 32 := by omega
  have hw2 : w < 2048 := by omega
  obtain ⟨t1, t2, l18, -, l19⟩ := rangeCheck_complete_low hl (e := t) (e' := 31 - t) (by omega) (by omega)
  obtain ⟨t3, t4, l22, -, l23⟩ := rangeCheck_complete_low hl (e := w) (e' := 2047 - w) (by omega) (by omega)
  have hsteps := windows_bwd hT hlen (by omega) hn hcells hcan hscr
  have hS := fun q (hq : q ≤ w) => cellsAt_four.mp (hscr q hq)
  obtain ⟨s00, s01, s02, s03⟩ := hS 0 (by omega)
  obtain ⟨sw0, sw1, sw2, sw3⟩ := hS w le_rfl
  simp only [Nat.mul_zero, pow_zero, mul_one, eOfNat_zero] at s00 s01 s02 s03
  rw [← pow4_eq _ w rfl] at sw0 sw1 sw2 sw3
  have hb := blocks_canonical hlen hcan
  have hl : ∀ r < 4, LoadHolds rd (p * gen ^ (128 * w) * gen ^ (4 * t)) r
      (cs.getD (4 * (n - 1) + r) 0) := fun r hr => by
    rw [mul_assoc, ← pow_add, loadHolds_mul_gen_pow,
      List.getD_eq_getElem _ _ (by omega), show 128 * w + 4 * t + r = 4 * (n - 1) + r by omega]
    exact hcells _ (by omega)
  have hlast : ![cs.getD (4 * (n - 1) + 0) 0, cs.getD (4 * (n - 1) + 1) 0,
      cs.getD (4 * (n - 1) + 2) 0, cs.getD (4 * (n - 1) + 3) 0] = blocksOf cs (n - 1) := by
    simp [blocksOf]
  have hmd : eOfNat (2 ^ 6 * n) + word 0 4294967295 0 = metadataCell (64 * n) true := by
    rw [md_final_word, eOfNat_add_metadataCell, Nat.xor_zero]; rfl
  refine ⟨t1, t2, t3, t4, ?_⟩
  simp only [cldBody, List.cons_append, List.nil_append, Stmt.HoldsList,
    Stmt.Holds, Atom.Holds, true_and, List.map_cons, List.map_nil]
  refine ⟨rfl, rfl, ?_, fun h => ?_, fun _ => ?_⟩
  · show IsInK (gen ^ n + word 1 0 0)
    rw [word_one, gen_pow_eq_ofK, ← ofK_one, ← ofK_add]; exact ofK_isInK _
  · exfalso
    have h' : gen ^ n + word 1 0 0 = 0 := h
    rw [word_one] at h'
    have := (gen_pow_eq_one_iff (by omega)).mp (e_add_eq_zero_iff.mp h')
    omega
  refine ⟨rfl, ⟨l18, ?_, l19⟩, rfl, ⟨l22, ?_, l23⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_,
    rfl, rfl, rfl, rfl, rfl, ?_, rfl, ?_, rfl, ?_, ?_, rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl, ?_, ?_,
    ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · show word 2147483648 0 0 = gen ^ t * gen ^ (31 - t)
    rw [word_g31, ← pow_add]; congr 1; omega
  · show word 55834575010 0 0 = gen ^ w * gen ^ (2047 - w)
    rw [word_g2047, ← pow_add]; congr 1; omega
  all_goals simp only [listVal, cldList, List.getD_cons_succ, List.getD_cons_zero]
  · rw [show gen ^ n * word 9223372036854775821 0 0 = gen ^ (32 * w + t) by
      rw [show gen ^ n = gen ^ (32 * w + t) * gen by rw [← pow_succ, hwt], mul_assoc,
        mul_comm gen, ginv_mul_gen, mul_one], e_add_eq_zero_iff]
    ring
  · rw [iv0_word]; exact s00
  · rw [iv1_word]; exact s01
  · rw [word_zero]; exact s02
  · exact s03
  · rw [word_one, gen_pow_eq_ofK, ← ofK_one, ← ofK_add]; exact ofK_isInK _
  · intro h
    rw [word_one, ← pow_zero gen]
    have hw0 : 0 < w := by
      rcases Nat.eq_zero_or_pos w with h0 | h0
      · exfalso; apply h; rw [h0, word_one, pow_zero, e_add_self]
      · exact h0
    exact (loop_iff (l86Step_mono rd c gsq) (l86_step rd (gen ^ w) c gsq) 0).mpr
      ⟨w, hw0, rfl, fun j h1 h2 he => by have := gen_pow_inj' (by omega) (by omega) he; omega,
        fun j _ h2 => hsteps j h2⟩
  · exact sw0
  · exact sw1
  · exact sw2
  · exact sw3
  · refine ⟨t, by simp [ctNames]; omega, (gen_pow_eq_ofK t), ?_⟩
    rw [← List.getD_eq_getElem _ "" (by simp [ctNames]; omega), claims_tail_iff t ht32]
    refine ⟨_, _, _, _, _, _, _, rfl, rfl, rfl, sliceOf cs (32 * w) t, length_sliceOf _ _ _, ?_, ?_⟩
    · rw [show 128 * w = 4 * (32 * w) by ring]
      exact cellsAt_sliceOf hcells (by omega)
    · refine (chainCells_prefix (blocksOf_sliceOf cs (32 * w) t)
        (fun j hj => baseMd_eq w j (by omega))).mpr ⟨fun j hj r => hb _ (by omega) r, ?_⟩
      rw [show 32 * w + t = n - 1 by omega]
  · exact (scaled_log_6_iff hT _ _).mpr ⟨_, rfl, n, hn, rfl, rfl⟩
  · exact hl 0 (by omega)
  · exact hl 1 (by omega)
  · exact hl 2 (by omega)
  · exact hl 3 (by omega)
  · rw [hlast, hmd]
    exact (final_iff hlen (by omega) (hb (n - 1) (by omega))).mpr hd

theorem claim_list_digest_iff {rd : Reader} (hm : MemOk rd) {gsq : E} (hT : SquaresAt rd gsq)
    (p n_g : E) (rets : List E) :
    coreProgram.Rel rd "claim_list_digest" [p, n_g, gsq] rets ↔
      Meaning_claim_list_digest rd [p, n_g, gsq] rets := by
  rw [rel_of_find find_claim_list_digest]
  simp only [Fn.Sem, cldBody, List.cons_append, List.nil_append, Stmt.HoldsList,
    Stmt.Holds, Atom.Holds, true_and, List.map_cons, List.map_nil]
  constructor
  · rintro ⟨σ, hp, c3, a4, hk4, hz, hnz⟩
    simp only [List.cons.injEq, and_true] at hp
    obtain ⟨rfl, rfl, rfl⟩ := hp
    by_cases h4 : σ (.n 4) = 0
    · obtain ⟨c5, c6, c7, c8, c9, c10, c11, hc, h60, h61, hr⟩ := hz h4
      have h1 : σ (.n 1) = 1 := by
        rw [a4, c3, word_one] at h4; exact e_add_eq_zero_iff.mp h4
      rw [c5, c6, c7, c8, c9, c10, c11, word_zero, iv0_word, iv1_word, md_final_word] at hc
      refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 60), σ (.n 61), rfl, hr.symm, 0, by norm_num,
        by rw [h1, pow_zero], [], rfl, cellsAt_nil _ _, by simp, ?_, Or.inl rfl⟩
      rw [h60, h61]
      exact blake2s_empty hc
    obtain ⟨c16, rc15, c20, rc14, m24, m25, m26, m27, m28, m29, c30, m31, ae, c32, m33, m34, m35,
      c37, l37, c38, l38, c39, l39, l0, c40, a41, c42, hk41, hloop, m43, m44, m45, l46, l47, l48,
      l49, ⟨t, ht, h15, htail⟩, hsl, c54, a55, l56, l57, l58, l59, hfin, h60, h61, hr⟩ := hnz h4
    -- the counts
    obtain ⟨w, e', hw32, he', h14, h21, h20⟩ := rangeCheck_sound hm rc14
    rw [c20, word_g2047] at h20
    have hw : w < 2048 := by have := gen_pow_inj' (by norm_num) (by omega) h20; omega
    have ht32 : t < 32 := by simpa [ctNames] using ht
    have h15' : σ (.n 15) = gen ^ t := by rw [h15, gen_pow_eq_ofK]
    have h28 : σ (.n 28) = gen ^ (32 * w) := by
      rw [m28, m27, m26, m25, m24, h14]; ring
    set n := 32 * w + t + 1 with hn
    have hng : σ (.n 1) = gen ^ n := by
      have e1 := e_add_eq_zero_iff.mp ae
      rw [m29, m31, c30, h28, h15'] at e1
      have : σ (.n 1) = σ (.n 1) * (word 9223372036854775821 0 0 * gen) := by
        rw [ginv_mul_gen, mul_one]
      rw [this, ← mul_assoc, ← e1, ← pow_add, ← pow_succ]
    obtain ⟨v, hv, N, hN, hN1, hN53⟩ := (scaled_log_6_iff hT _ _).mp hsl
    simp only [List.cons.injEq, and_true] at hv
    have hNn : N = n := gen_pow_inj' (lt_trans hN (by norm_num)) (by omega) (hN1.symm.trans hng)
    subst hNn
    -- the windows
    have h0c : CellsAt rd (σ (.n 36)) [(digestScalars paramIv).1, (digestScalars paramIv).2, 0,
        σ (.n 0)] := by
      rw [cellsAt_four, ← iv0_word, ← iv1_word, ← word_zero, ← c37, ← c38, ← c39]
      exact ⟨l37, l38, l39, l0⟩
    have hsteps : ∀ j < w, L86Step rd (σ (.n 36)) (σ (.n 2)) (coreProgram.Rel rd) (gen ^ j) := by
      intro j hj
      have hne : σ (.n 41) ≠ 0 := by
        rw [a41, c40, word_one, h14]
        intro h
        have := (gen_pow_eq_one_iff (by omega)).mp (e_add_eq_zero_iff.mp h).symm
        omega
      have hl := hloop hne
      rw [c42, word_one, ← pow_zero gen] at hl
      exact loop86_iters h14 (by omega) hl j hj
    have hwin := windows_fwd (len := 4 * n) hT (by omega) (by omega) h0c hsteps
    obtain ⟨hIw, hcanw, hldw⟩ := hwin w le_rfl
    have h45 : σ (.n 45) = σ (.n 36) * gen ^ (4 * w) := by rw [m45, m44, m43, pow4_eq _ w h14]
    rw [h45] at l46 l47 l48 l49
    rw [cellsAt_four] at hIw
    have e46 := loadHolds_unique l46 hIw.1
    have e47 := loadHolds_unique l47 hIw.2.1
    have e48 := loadHolds_unique l48 hIw.2.2.1
    have e49 := loadHolds_unique l49 hIw.2.2.2
    -- the tail
    rw [← List.getD_eq_getElem _ "" ht, claims_tail_iff t ht32] at htail
    obtain ⟨_, _, _, _, _, _, _, hargs, hrets, hp', cst, hlent, hcellst, hcht⟩ := htail
    simp only [List.cons.injEq, and_true] at hargs hrets
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hargs
    obtain ⟨rfl, rfl, rfl⟩ := hrets
    rw [e49, show 128 * w = 4 * (32 * w) by ring] at hcellst
    have hbt := blocksOf_slice (len := 4 * n) (b := 32 * w) t hcellst hlent (by omega)
    rw [e46, e47, e48, chainCells_prefix (k := 32 * w) hbt (fun j hj => by
      rw [show 32 * w = 32 * w from rfl]; exact baseMd_eq w j (by omega))] at hcht
    obtain ⟨hcant, hout⟩ := hcht
    -- the last block
    have h52 : σ (.n 52) = σ (.n 0) * gen ^ (4 * (n - 1)) := by
      rw [hp', e49, mul_assoc, ← pow_add]; congr 2; omega
    rw [h52] at l56 l57 l58 l59
    rw [loadHolds_mul_gen_pow] at l56 l57 l58 l59
    rw [Nat.add_zero] at l56
    set cs := cellsFrom rd (σ (.n 0)) (4 * n) with hcs
    have hlast : blocksOf cs (n - 1) = ![σ (.n 56), σ (.n 57), σ (.n 58), σ (.n 59)] := by
      have hr : ∀ r < 4, cs.getD (4 * (n - 1) + r) 0 = cellAt rd (σ (.n 0)) (4 * (n - 1) + r) :=
        fun r hr => cellsFrom_getD (by omega)
      have r0 := hr 0 (by omega)
      rw [Nat.add_zero] at r0
      simp only [blocksOf, r0, hr 1 (by omega), hr 2 (by omega), hr 3 (by omega),
        cellAt_of_load l56, cellAt_of_load l57, cellAt_of_load l58, cellAt_of_load l59]
    have h55 : σ (.n 55) = metadataCell (64 * n) true := by
      rw [a55, c54, hv, hN53, md_final_word, eOfNat_add_metadataCell, Nat.xor_zero]; rfl
    rw [← hlast, h55] at hfin
    rw [show 32 * w + t = n - 1 by omega] at hout
    have hout1 := congrArg Prod.fst hout
    have hout2 := congrArg Prod.snd hout
    simp only at hout1 hout2
    rw [hout1, hout2] at hfin
    have hcanl := (compressCells_canonical hfin).1
    have hcan : ∀ j < n, ∀ r, IsCanonical128 (blocksOf cs j r) := by
      intro j hj
      rcases (show j < 32 * w ∨ 32 * w ≤ j ∧ j < 32 * w + t ∨ j = n - 1 by omega) with h | ⟨h1, h2⟩ | rfl
      · exact hcanw j h
      · have := hcant (j - 32 * w) (by omega)
        rwa [show 32 * w + (j - 32 * w) = j by omega] at this
      · exact hcanl
    have hlen : cs.length = 4 * n := length_cellsFrom _ _ _
    refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 60), σ (.n 61), rfl, hr.symm, n, hN, hng, cs, hlen,
      ?_, canonical_of_blocks hlen hcan, ?_, Or.inr ⟨σ (.n 36), fun q hq => ?_⟩⟩
    · intro i hi
      rw [hlen] at hi
      simp only [hcs, cellsFrom, List.getElem_map, List.getElem_range]
      rcases (show i < 128 * w ∨ 128 * w ≤ i ∧ i < 128 * w + 4 * t ∨ 4 * (n - 1) ≤ i by omega)
        with h | ⟨h1, h2⟩ | h
      · exact hldw i h
      · have := loads_slice hcellst (i - 4 * (32 * w)) (by omega)
        rwa [show 4 * (32 * w) + (i - 4 * (32 * w)) = i by omega] at this
      · obtain ⟨r, hr4, rfl⟩ : ∃ r, r < 4 ∧ i = 4 * (n - 1) + r := ⟨i - 4 * (n - 1), by omega, by omega⟩
        interval_cases r
        · rw [Nat.add_zero]; exact load_cellAt l56
        · exact load_cellAt l57
        · exact load_cellAt l58
        · exact load_cellAt l59
    · rw [h60, h61]
      exact (final_iff hlen (by omega) hcanl).mp hfin
    · exact (hwin q (by omega)).1
  · rintro ⟨p', n_g', gsq', d0, d1, hargs, rfl, n, hn, hng, cs, hlen, hcells, hcan, hd, hscr⟩
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl⟩ := hargs
    rcases Nat.eq_zero_or_pos n with rfl | hn1
    · rw [pow_zero] at hng
      subst hng
      rw [Nat.mul_zero, List.length_eq_zero_iff] at hlen
      subst hlen
      have h11 : (1 : E) + word 1 0 0 = 0 := by rw [word_one, e_add_self]
      refine ⟨listVal ([p, 1, gsq, word 1 0 0, 1 + word 1 0 0, word 0 0 0, word 0 0 0, word 0 0 0,
        word 0 0 0, word 13503953895743350343 11912009169889063794 0,
        word 11170449402626986623 6620516960021240235 0, word 0 4294967295 0, d0, d1] ++
        List.replicate 46 0 ++ [d0, d1]), rfl, rfl, rfl, ?_, fun _ => ?_, fun h => ?_⟩
      · show IsInK ((1 : E) + word 1 0 0)
        rw [h11, ← ofK_zero]; exact ofK_isInK _
      · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
        show CompressCells ![word 0 0 0, word 0 0 0, word 0 0 0, word 0 0 0]
          (word 13503953895743350343 11912009169889063794 0)
          (word 11170449402626986623 6620516960021240235 0) d0 d1 (word 0 4294967295 0)
        rw [word_zero, iv0_word, iv1_word, md_final_word]
        exact compressCells_empty_iff.mpr hd
      · exfalso; apply h; show (1 : E) + word 1 0 0 = 0; exact h11
    · rcases hscr with h0 | ⟨c, hscr⟩
      · omega
      subst hng
      obtain ⟨t1, t2, t3, t4, h⟩ := cld_holds_pos hm.low16 hT hn hn1 hlen hcells hcan hscr hd
      simp only [cldBody, List.cons_append, List.nil_append, Stmt.HoldsList,
        Stmt.Holds, Atom.Holds, true_and, List.map_cons, List.map_nil] at h
      exact ⟨listVal (cldList p gsq c d0 d1 cs n _ _ t1 t2 t3 t4), rfl, h⟩


/-- Completeness, for every pointer `chain` of the windows' `HeapBuf` holding their honest
states. -/
theorem claim_list_digest_complete {rd : Reader} (hm : MemOk rd) {gsq : E}
    (hT : SquaresAt rd gsq) (chain ptr : E) {n : ℕ} (hn : n < 2 ^ 16) {cs : List E}
    (hlen : cs.length = 4 * n) (hcs : CellsAt rd ptr cs) (hcan : ∀ c ∈ cs, IsCanonical128 c)
    (hS : 0 < n → ClScratch rd ptr chain cs ((n - 1) / 32)) :
    coreProgram.Rel rd "claim_list_digest" [ptr, gen ^ n, gsq]
      [(digestScalars (blake2sBytes (cs.flatMap cellBytes))).1,
        (digestScalars (blake2sBytes (cs.flatMap cellBytes))).2] :=
  (claim_list_digest_iff hm hT _ _ _).mpr ⟨ptr, _, gsq, _, _, rfl, rfl, n, hn, rfl, cs, hlen, hcs,
    hcan, rfl, (Nat.eq_zero_or_pos n).imp id fun h => ⟨chain, hS h⟩⟩

end
end LeanVM.Guest.B1.Digest

namespace LeanVM.Guest.B1
export Digest (ClScratch Meaning_claim_list_digest claim_list_digest_iff claim_list_digest_complete)
end LeanVM.Guest.B1
