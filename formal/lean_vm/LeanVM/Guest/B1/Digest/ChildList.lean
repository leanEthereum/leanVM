/-
  LeanVM.Guest.B1.Digest.ChildList

  B1 for `child_claim_list_digest` (G:2844-2880; TRIAGE #65) and its window loop `__loop87`: a
  child's claim list digest, rebuilt from this node's table at hinted indices, every claim marking
  its coverage slot.
-/

module

public import LeanVM.Guest.B1.Digest.ChildWindow
public import LeanVM.Guest.B1.Digest.ClaimList

/-!
# `child_claim_list_digest`

`child_claim_list_digest(entries, cover, base, origin, limit, n_g, g_squares)`: for `n_g = g^n`,
the BLAKE2s of `n` claims, claim `i` read at the table entry `entries·g^(4·off i)`, its index
below `log limit`, and the coverage slot `cover·(origin·g^(off i))` holding `base·g^i`
(`ChildReads … base … n`). The marks are distinct for distinct `i < n`, and a write-once memory
holds one word per slot, so two claims of the list never share a slot; `main` concludes the
coverage from these marks and its count (`Pigeonhole.cover_of_writeOnce`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-! ## `__loop87` -/

/-- `__loop87`'s body. -/
def l87Body : List Stmt :=
  ([.mul (.n 9) (.n 0) (.n 0), .mul (.n 10) (.n 9) (.n 9), .mul (.n 11) (.n 2) (.n 10),
    .mul (.n 12) (.n 0) (.n 0), .mul (.n 13) (.n 12) (.n 12), .mul (.n 14) (.n 13) (.n 13),
    .mul (.n 15) (.n 14) (.n 14), .mul (.n 16) (.n 15) (.n 15), .mul (.n 17) (.n 3) (.n 16),
    .load (.n 18) (.n 11) 0, .load (.n 19) (.n 11) 1, .load (.n 20) (.n 11) 2] : List Atom).map .atom ++
  [.call "child_claims_window" [.n 18, .n 19, .n 20, .n 4, .n 5, .n 17, .n 6, .n 7, .n 0, .n 8]
    [.n 21, .n 22, .n 23]] ++
  ([.const (.n 24) (word 2 0 0), .mul (.n 25) (.n 0) (.n 24), .mul (.n 26) (.n 25) (.n 25),
    .mul (.n 27) (.n 26) (.n 26), .mul (.n 28) (.n 2) (.n 27), .load (.n 21) (.n 28) 0,
    .load (.n 22) (.n 28) 1, .load (.n 23) (.n 28) 2, .const (.n 29) (word 2 0 0),
    .mul (.n 30) (.n 0) (.n 29), .add (.n 31) (.n 30) (.n 1), .const (.n 32) (word 2 0 0),
    .mul (.n 33) (.n 0) (.n 32)] : List Atom).map .atom ++
  [.callIf (.n 31) "__loop87" [.n 33, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8], .ret []]

set_option maxRecDepth 100000 in
theorem find_loop87 : coreProgram.find? "__loop87" =
    some ⟨"__loop87", [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8], l87Body⟩ :=
  Program.find?_of_indexOf? (j := 496) (by decide +kernel) rfl

/-- `x^32` as `__loop87` squares it. -/
def pow32 (x : E) : E :=
  x * x * (x * x) * (x * x * (x * x)) * (x * x * (x * x) * (x * x * (x * x))) *
    (x * x * (x * x) * (x * x * (x * x)) * (x * x * (x * x) * (x * x * (x * x))))

theorem pow32_eq (q : ℕ) : pow32 (gen ^ q) = gen ^ (32 * q) := by
  unfold pow32; ring

/-- One iteration of `__loop87` at `x`: the window's slot at `chain·x⁴` (state and base), the
window run with marks `base·x^32`, its results stored at `chain·(x·g)⁴`. -/
def L87Step (rd : Reader) (chain base entries cover origin limit gsq : E) (C : CallRel) (x : E) :
    Prop :=
  ∃ s0 s1 bs o0 o1 nxt, CellsAt rd (chain * (x * x * (x * x))) [s0, s1, bs] ∧
    C "child_claims_window" [s0, s1, bs, entries, cover, base * pow32 x, origin, limit, x, gsq]
      [o0, o1, nxt] ∧
    CellsAt rd (chain * (x * gen * (x * gen) * (x * gen * (x * gen)))) [o0, o1, nxt]

theorem l87Step_mono (rd : Reader) (c base entries cover origin limit gsq : E) :
    ∀ C C' x, CallRel.Le C C' → L87Step rd c base entries cover origin limit gsq C x →
      L87Step rd c base entries cover origin limit gsq C' x :=
  fun _ _ _ hC ⟨a, b, d, e, f, g, h1, h2, h3⟩ => ⟨a, b, d, e, f, g, h1, hC _ _ _ h2, h3⟩

theorem cellsAt_three {rd : Reader} {p r0 r1 r2 : E} :
    CellsAt rd p [r0, r1, r2] ↔ LoadHolds rd p 0 r0 ∧ LoadHolds rd p 1 r1 ∧ LoadHolds rd p 2 r2 := by
  constructor
  · intro h
    exact ⟨h 0 (by simp), h 1 (by simp), h 2 (by simp)⟩
  · rintro ⟨h0, h1, h2⟩ k hk
    simp only [List.length_cons, List.length_nil] at hk
    rcases k with _ | _ | _ | k
    exacts [h0, h1, h2, absurd hk (by omega)]

theorem l87_step (rd : Reader) (W c base entries cover origin limit gsq : E) (C : CallRel) (x : E) :
    (∃ fn, coreProgram.find? "__loop87" = some fn ∧
        fn.Sem C rd (x :: [W, c, base, entries, cover, origin, limit, gsq]) []) ↔
      L87Step rd c base entries cover origin limit gsq C x ∧ IsInK (x * gen + W) ∧
        (x * gen + W ≠ 0 → C "__loop87" (x * gen :: [W, c, base, entries, cover, origin, limit, gsq]) []) := by
  have hf : ∀ fn, coreProgram.find? "__loop87" = some fn ↔
      fn = ⟨"__loop87", [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8], l87Body⟩ := fun fn => by
    rw [find_loop87]; exact ⟨fun h => (Option.some.inj h).symm, fun h => by rw [h]⟩
  simp only [hf, exists_eq_left]
  simp only [Fn.Sem, l87Body, List.cons_append, List.nil_append, Stmt.HoldsList,
    Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, L87Step, cellsAt_three, ← word_gen]
  constructor
  · rintro ⟨σ, hp, m9, m10, m11, m12, m13, m14, m15, m16, m17, l18, l19, l20, hcall, c24, m25, m26,
      m27, m28, l21, l22, l23, c29, m30, a31, c32, m33, hk, hnext, -⟩
    simp only [List.cons.injEq, and_true] at hp
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hp
    rw [m11, m10, m9] at l18 l19 l20
    rw [m28, m27, m26, m25, c24] at l21 l22 l23
    rw [m17, m16, m15, m14, m13, m12] at hcall
    rw [a31, m30, c29] at hk hnext
    rw [m33, c32] at hnext
    exact ⟨⟨_, _, _, _, _, _, ⟨l18, l19, l20⟩, hcall, ⟨l21, l22, l23⟩⟩, hk, hnext⟩
  · rintro ⟨⟨s0, s1, bs, o0, o1, nxt, ⟨l18, l19, l20⟩, hcall, ⟨l21, l22, l23⟩⟩, hk, hnext⟩
    refine ⟨listVal [x, W, c, base, entries, cover, origin, limit, gsq, x * x, x * x * (x * x),
      c * (x * x * (x * x)), x * x, x * x * (x * x), x * x * (x * x) * (x * x * (x * x)),
      x * x * (x * x) * (x * x * (x * x)) * (x * x * (x * x) * (x * x * (x * x))), pow32 x,
      base * pow32 x, s0, s1, bs, o0, o1, nxt, word 2 0 0, x * word 2 0 0,
      x * word 2 0 0 * (x * word 2 0 0),
      x * word 2 0 0 * (x * word 2 0 0) * (x * word 2 0 0 * (x * word 2 0 0)),
      c * (x * word 2 0 0 * (x * word 2 0 0) * (x * word 2 0 0 * (x * word 2 0 0))), word 2 0 0,
      x * word 2 0 0, x * word 2 0 0 + W, word 2 0 0, x * word 2 0 0], rfl, ?_⟩
    simp only [listVal, List.getD_cons_succ, List.getD_cons_zero, true_and]
    exact ⟨rfl, l18, l19, l20, hcall, l21, l22, l23, hk, hnext, trivial⟩

/-! ## `child_claim_list_digest` -/

/-- The scratch table of a child's claim list: window `q ≤ w` at `chain·g^(4q)`, its state after
`32q` blocks and its base `E(2^11·q)`. -/
def ChildScratch (rd : Reader) (chain : E) (cs : List E) (w : ℕ) : Prop :=
  ∀ q ≤ w, CellsAt rd (chain * gen ^ (4 * q)) [(digestScalars (prefixDigest cs (32 * q))).1,
    (digestScalars (prefixDigest cs (32 * q))).2, eOfNat (2 ^ 11 * q)]

/-- **`child_claim_list_digest(entries, cover, base, origin, limit, n_g, g_squares)`**:
`n_g = g^n`, `n < 2^16`, and the digest is the BLAKE2s of `n` canonical claims, claim `i` read
at the table index `off i` below `log limit` and marking its slot with `base·g^i`
(`ChildReads … base … n`); the windows' scratch table holds their states. -/
def Meaning_child_claim_list_digest (rd : Reader) (args rets : List E) : Prop :=
  ∃ entries cover base origin limit n_g gsq d0 d1,
    args = [entries, cover, base, origin, limit, n_g, gsq] ∧ rets = [d0, d1] ∧
    ∃ n < 2 ^ 16, n_g = gen ^ n ∧ ∃ (off : ℕ → ℕ) (cs : List E), cs.length = 4 * n ∧
      ChildReads rd entries cover base origin limit off cs n ∧ (∀ c ∈ cs, IsCanonical128 c) ∧
      (d0, d1) = digestScalars (blake2sBytes (cs.flatMap cellBytes)) ∧
      (n = 0 ∨ ∃ chain, ChildScratch rd chain cs ((n - 1) / 32))

/-- `child_claim_list_digest`'s body. -/
def ccldBody : List Stmt :=
  [.atom (.const (.n 7) (word 1 0 0)), .atom (.add (.n 8) (.n 5) (.n 7)),
   .ite (.n 8)
    (([.const (.n 9) (word 0 0 0), .const (.n 10) (word 0 0 0), .const (.n 11) (word 0 0 0),
      .const (.n 12) (word 0 0 0), .const (.n 13) (word 13503953895743350343 11912009169889063794 0),
      .const (.n 14) (word 11170449402626986623 6620516960021240235 0),
      .const (.n 15) (word 0 4294967295 0),
      .blake2s (.n 9) (.n 10) (.n 11) (.n 12) (.n 13) (.n 14) (.n 16) (.n 17) (.n 15)] :
      List Atom).map .atom)
    (([.hint (.witness "signers_split" (.stack [.n 18, .n 19])),
      .const (.n 20) (word 2147483648 0 0), .rangeCheck (.n 19) (.n 21) (.n 22) (.n 23) (.n 20),
      .const (.n 24) (word 55834575010 0 0), .rangeCheck (.n 18) (.n 25) (.n 26) (.n 27) (.n 24),
      .mul (.n 28) (.n 18) (.n 18), .mul (.n 29) (.n 28) (.n 28), .mul (.n 30) (.n 29) (.n 29),
      .mul (.n 31) (.n 30) (.n 30), .mul (.n 32) (.n 31) (.n 31), .mul (.n 33) (.n 32) (.n 19),
      .const (.n 34) (word 9223372036854775821 0 0), .mul (.n 35) (.n 5) (.n 34),
      .assertEq (.n 33) (.n 35), .const (.n 36) (word 2 0 0), .mul (.n 37) (.n 18) (.n 36),
      .mul (.n 38) (.n 37) (.n 37), .mul (.n 39) (.n 38) (.n 38), .hint (.allocDyn (.n 40) (.n 39)),
      .const (.n 41) (word 13503953895743350343 11912009169889063794 0), .load (.n 41) (.n 40) 0,
      .const (.n 42) (word 11170449402626986623 6620516960021240235 0), .load (.n 42) (.n 40) 1,
      .const (.n 43) (word 0 0 0), .load (.n 43) (.n 40) 2, .const (.n 44) (word 1 0 0),
      .add (.n 45) (.n 44) (.n 18), .const (.n 46) (word 1 0 0)] : List Atom).map .atom ++
    [.callIf (.n 45) "__loop87" [.n 46, .n 18, .n 40, .n 2, .n 0, .n 1, .n 3, .n 4, .n 6]] ++
    ([.mul (.n 47) (.n 18) (.n 18), .mul (.n 48) (.n 47) (.n 47), .mul (.n 49) (.n 40) (.n 48),
      .mul (.n 50) (.n 18) (.n 18), .mul (.n 51) (.n 50) (.n 50), .mul (.n 52) (.n 51) (.n 51),
      .mul (.n 53) (.n 52) (.n 52), .mul (.n 54) (.n 53) (.n 53), .mul (.n 55) (.n 2) (.n 54),
      .load (.n 56) (.n 49) 0, .load (.n 57) (.n 49) 1, .load (.n 58) (.n 49) 2] :
      List Atom).map .atom ++
    [.dispatch (.n 19) cctNames [.n 56, .n 57, .n 58, .n 0, .n 1, .n 55, .n 3, .n 4] [.n 59, .n 60]] ++
    ([.hint (.witness "child_claim_index" (.stack [.n 61])),
      .const (.n 62) (word 9223372036854775821 0 0), .mul (.n 63) (.n 4) (.n 62),
      .rangeCheck (.n 61) (.n 64) (.n 65) (.n 66) (.n 63),
      .const (.n 67) (word 9223372036854775821 0 0), .mul (.n 68) (.n 5) (.n 67),
      .mul (.n 69) (.n 2) (.n 68), .mul (.n 70) (.n 3) (.n 61), .mul (.n 71) (.n 1) (.n 70),
      .load (.n 69) (.n 71) 0, .mul (.n 72) (.n 61) (.n 61), .mul (.n 73) (.n 72) (.n 72),
      .mul (.n 74) (.n 0) (.n 73)] : List Atom).map .atom ++
    [.call "scaled_log__L6" [.n 5, .n 6] [.n 75]] ++
    ([.const (.n 76) (word 0 4294967295 0), .add (.n 77) (.n 75) (.n 76), .load (.n 78) (.n 74) 0,
      .load (.n 79) (.n 74) 1, .load (.n 80) (.n 74) 2, .load (.n 81) (.n 74) 3,
      .blake2s (.n 78) (.n 79) (.n 80) (.n 81) (.n 59) (.n 60) (.n 16) (.n 17) (.n 77)] :
      List Atom).map .atom),
   .atom (.copy (.n 82) (.n 16)), .atom (.copy (.n 83) (.n 17)), .ret [.n 82, .n 83]]

set_option maxRecDepth 100000 in
theorem find_child_claim_list_digest : coreProgram.find? "child_claim_list_digest" =
    some ⟨"child_claim_list_digest", [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6], ccldBody⟩ :=
  Program.find?_of_indexOf? (j := 22) (by decide +kernel) rfl

/-! ## Forward -/

/-- The cells a child's list reads, from the table at the indices `off`. -/
noncomputable def csOf (rd : Reader) (entries : E) (off : ℕ → ℕ) (len : ℕ) : List E :=
  (List.range len).map fun k => cellAt rd entries (4 * off (k / 4) + k % 4)

theorem csOf_getD {rd : Reader} {entries : E} {off : ℕ → ℕ} {len j r : ℕ} (hr : r < 4)
    (h : 4 * j + r < len) : (csOf rd entries off len).getD (4 * j + r) 0 =
      cellAt rd entries (4 * off j + r) := by
  rw [csOf, List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map, List.getElem_range]
  rw [show (4 * j + r) / 4 = j by omega, show (4 * j + r) % 4 = r by omega]

theorem length_csOf (rd : Reader) (entries : E) (off : ℕ → ℕ) (len : ℕ) :
    (csOf rd entries off len).length = len := by simp [csOf]

/-- A block read through the table entry `entries·g^(4e)` is the table's cells there. -/
theorem block_of_entry {rd : Reader} {entries : E} {e : ℕ} {a0 a1 a2 a3 : E}
    (h : CellsAt rd (entries * gen ^ (4 * e)) [a0, a1, a2, a3]) :
    a0 = cellAt rd entries (4 * e) ∧ a1 = cellAt rd entries (4 * e + 1) ∧
      a2 = cellAt rd entries (4 * e + 2) ∧ a3 = cellAt rd entries (4 * e + 3) :=
  ⟨by simpa using (cellsAt_slice h 0 (by simp)).1, (cellsAt_slice h 1 (by simp)).1,
    (cellsAt_slice h 2 (by simp)).1, (cellsAt_slice h 3 (by simp)).1⟩

/-- The table's cells read through an entry, back as a `CellsAt`. -/
theorem entry_of_reads {rd : Reader} {entries : E} {e : ℕ} {a0 a1 a2 a3 : E}
    (h : CellsAt rd (entries * gen ^ (4 * e)) [a0, a1, a2, a3]) :
    CellsAt rd (entries * gen ^ (4 * e)) [cellAt rd entries (4 * e), cellAt rd entries (4 * e + 1),
      cellAt rd entries (4 * e + 2), cellAt rd entries (4 * e + 3)] := by
  obtain ⟨e0, e1, e2, e3⟩ := block_of_entry h
  rw [← e0, ← e1, ← e2, ← e3]; exact h

theorem blocksOf_csOf {rd : Reader} {entries : E} {off : ℕ → ℕ} {len j : ℕ} (h : 4 * j + 3 < len) :
    blocksOf (csOf rd entries off len) j = ![cellAt rd entries (4 * off j),
      cellAt rd entries (4 * off j + 1), cellAt rd entries (4 * off j + 2),
      cellAt rd entries (4 * off j + 3)] := by
  have e0 : (csOf rd entries off len).getD (4 * j) 0 = cellAt rd entries (4 * off j) := by
    simpa using csOf_getD (j := j) (r := 0) (off := off) (rd := rd) (entries := entries) (by omega) (by omega)
  rw [blocksOf_getD, e0, csOf_getD (by omega) (by omega), csOf_getD (by omega) (by omega),
    csOf_getD (by omega) (by omega)]

/-- **The child's windows, forward**: with the indices `off` of the windows' reads, `w` loop
iterations establish the scratch table and the canonicity and the reads of the first `32w`
blocks of the table's cells. -/
theorem cwins_fwd {rd : Reader} {c base entries cover origin limit : E} {len w : ℕ} {off : ℕ → ℕ}
    (hw : 128 * w ≤ len)
    (h0 : CellsAt rd c [(digestScalars paramIv).1, (digestScalars paramIv).2, 0])
    (hW : ∀ q < w, ∃ s0 s1 bs o0 o1 nxt csq, CellsAt rd (c * gen ^ (4 * q)) [s0, s1, bs] ∧
      CellsAt rd (c * gen ^ (4 * (q + 1))) [o0, o1, nxt] ∧ csq.length = 128 ∧
      ChildReads rd entries cover (base * gen ^ (32 * q)) origin limit (fun j => off (32 * q + j)) csq 32 ∧
      ChainCells (s0, s1) (blocksOf csq) (windowMd bs nxt) 32 (o0, o1) ∧
      nxt = eOfNat (2 ^ 11 * (q + 1))) :
    ∀ q ≤ w, CellsAt rd (c * gen ^ (4 * q))
        [(digestScalars (prefixDigest (csOf rd entries off len) (32 * q))).1,
          (digestScalars (prefixDigest (csOf rd entries off len) (32 * q))).2, eOfNat (2 ^ 11 * q)] ∧
      (∀ j < 32 * q, ∀ r, IsCanonical128 (blocksOf (csOf rd entries off len) j r)) ∧
      ChildReads rd entries cover base origin limit off (csOf rd entries off len) (32 * q) := by
  intro q hq
  induction q with
  | zero =>
    refine ⟨?_, fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega)⟩
    simpa [eOfNat_zero, prefixDigest, absorbBlocks] using h0
  | succ q ih =>
    obtain ⟨hI, hcan, hR⟩ := ih (by omega)
    obtain ⟨s0, s1, bs, o0, o1, nxt, csq, hslot, hstore, hlen, hRq, hch, hnxt⟩ := hW q (by omega)
    rw [cellsAt_three] at hslot hI
    have e0 := loadHolds_unique hslot.1 hI.1
    have e1 := loadHolds_unique hslot.2.1 hI.2.1
    have e2 := loadHolds_unique hslot.2.2 hI.2.2
    subst e0 e1 e2
    have hb : ∀ j < 32, blocksOf csq j = blocksOf (csOf rd entries off len) (32 * q + j) := by
      intro j hj
      obtain ⟨-, -, hc⟩ := hRq j hj
      obtain ⟨a0, a1, a2, a3⟩ := block_of_entry hc
      rw [blocksOf_csOf (by omega), blocksOf_getD, a0, a1, a2, a3]
    rw [chainCells_prefix (k := 32 * q) hb (fun j hj => by rw [hnxt]; exact windowMd_eq q j hj)] at hch
    obtain ⟨hcan', hout⟩ := hch
    refine ⟨?_, fun j hj => ?_, fun i hi => ?_⟩
    · rw [cellsAt_three] at hstore ⊢
      rw [show 32 * (q + 1) = 32 * q + 32 by ring, ← hout, ← hnxt]
      exact hstore
    · rcases Nat.lt_or_ge j (32 * q) with h | h
      · exact hcan j h
      · have := hcan' (j - 32 * q) (by omega)
        rwa [show 32 * q + (j - 32 * q) = j by omega] at this
    · rcases Nat.lt_or_ge i (32 * q) with h | h
      · exact hR i h
      · obtain ⟨hL, hs, hc⟩ := hRq (i - 32 * q) (by omega)
        dsimp only at hL hs hc
        rw [show 32 * q + (i - 32 * q) = i by omega] at hL hs hc
        rw [mul_assoc, ← pow_add, show 32 * q + (i - 32 * q) = i by omega] at hs
        refine ⟨hL, hs, ?_⟩
        have hc' := entry_of_reads hc
        have e0 : (csOf rd entries off len).getD (4 * i) 0 = cellAt rd entries (4 * off i) := by
          simpa using csOf_getD (j := i) (r := 0) (off := off) (rd := rd) (entries := entries)
            (by omega) (by omega)
        rw [e0, csOf_getD (by omega) (by omega), csOf_getD (by omega) (by omega),
          csOf_getD (by omega) (by omega)]
        exact hc'

/-- **`__loop87`** from `g^k` to `W`: `W = g^m` for the first `m > k` the loop reaches, every
iteration `g^j`, `k ≤ j < m`, holding. -/
theorem loop87_iff (rd : Reader) (W c base entries cover origin limit gsq : E) (k : ℕ) :
    coreProgram.Rel rd "__loop87" (gen ^ k :: [W, c, base, entries, cover, origin, limit, gsq]) [] ↔
      ∃ m, k < m ∧ W = gen ^ m ∧ (∀ j, k < j → j < m → gen ^ j ≠ W) ∧
        ∀ j, k ≤ j → j < m →
          L87Step rd c base entries cover origin limit gsq (coreProgram.Rel rd) (gen ^ j) :=
  loop_iff (l87Step_mono rd c base entries cover origin limit gsq)
    (l87_step rd W c base entries cover origin limit gsq) k

/-- The loop's iterations, from the entry `callIf`: `w` of them, at `g^j`, `j < w`. -/
theorem loop87_iters {rd : Reader} {W c base entries cover origin limit gsq : E} {w : ℕ}
    (hW : W = gen ^ w) (hw : w < 2 ^ 33)
    (h : coreProgram.Rel rd "__loop87" [gen ^ 0, W, c, base, entries, cover, origin, limit, gsq] []) :
    ∀ j < w, L87Step rd c base entries cover origin limit gsq (coreProgram.Rel rd) (gen ^ j) := by
  intro j hj
  obtain ⟨m, hm0, hmN, hfirst, hall⟩ :=
    (loop_iff (l87Step_mono rd c base entries cover origin limit gsq)
      (l87_step rd W c base entries cover origin limit gsq) 0).mp h
  have hmw : m = w := by
    rcases Nat.lt_or_ge w m with hlt | hge
    · exact absurd hW.symm (hfirst w (by omega) hlt)
    · exact gen_pow_inj' (by omega) hw (hmN.symm.trans hW)
  exact hall j (by omega) (by omega)

theorem child_claim_list_digest_fwd {rd : Reader} (hm : MemOk rd) {gsq : E}
    (hT : SquaresAt rd gsq) {entries cover base origin limit n_g : E} {rets : List E}
    (h : coreProgram.Rel rd "child_claim_list_digest" [entries, cover, base, origin, limit, n_g, gsq]
      rets) :
    Meaning_child_claim_list_digest rd [entries, cover, base, origin, limit, n_g, gsq] rets := by
  rw [rel_of_find find_child_claim_list_digest] at h
  simp only [Fn.Sem, ccldBody, List.cons_append, List.nil_append, Stmt.HoldsList,
    Stmt.Holds, Atom.Holds, true_and, List.map_cons, List.map_nil] at h
  obtain ⟨σ, hp, c7, a8, hk8, hz, hnz⟩ := h
  simp only [List.cons.injEq, and_true] at hp
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hp
  by_cases h8 : σ (.n 8) = 0
  · obtain ⟨c9, c10, c11, c12, c13, c14, c15, hc, h82, h83, hr⟩ := hz h8
    have h1 : σ (.n 5) = 1 := by
      rw [a8, c7, word_one] at h8; exact e_add_eq_zero_iff.mp h8
    rw [c9, c10, c11, c12, c13, c14, c15, word_zero, iv0_word, iv1_word, md_final_word] at hc
    refine ⟨_, _, _, _, _, _, _, σ (.n 82), σ (.n 83), rfl, hr.symm, 0, by norm_num,
      by rw [h1, pow_zero], fun _ => 0, [], rfl, fun j hj => absurd hj (by omega), by simp, ?_,
      Or.inl rfl⟩
    rw [h82, h83]
    exact blake2s_empty hc
  obtain ⟨c20, rc19, c24, rc18, m28, m29, m30, m31, m32, m33, c34, m35, ae, c36, m37, m38, m39,
    c41, l41, c42, l42, c43, l43, c44, a45, c46, hk45, hloop, m47, m48, m49, m50, m51, m52, m53,
    m54, m55, l56, l57, l58, ⟨t, ht, h19, htail⟩, c62, m63, rc61, c67, m68, m69, m70, m71, lmark,
    m72, m73, m74, hsl, c76, a77, l78, l79, l80, l81, hfin, h82, h83, hr⟩ := hnz h8
  -- the counts
  obtain ⟨w, e', hw32, he', h18, h25, h24⟩ := rangeCheck_sound hm rc18
  rw [c24, word_g2047] at h24
  have hw : w < 2048 := by have := gen_pow_inj' (by norm_num) (by omega) h24; omega
  have ht32 : t < 32 := by simpa [cctNames] using ht
  have h19' : σ (.n 19) = gen ^ t := by rw [h19, gen_pow_eq_ofK]
  have h32 : σ (.n 32) = gen ^ (32 * w) := by
    rw [m32, m31, m30, m29, m28, h18]; ring
  set n := 32 * w + t + 1 with hn
  have hng : σ (.n 5) = gen ^ n := by
    have e1 := e_add_eq_zero_iff.mp ae
    rw [m33, m35, c34, h32, h19'] at e1
    have : σ (.n 5) = σ (.n 5) * (word 9223372036854775821 0 0 * gen) := by
      rw [ginv_mul_gen, mul_one]
    rw [this, ← mul_assoc, ← e1, ← pow_add, ← pow_succ]
  obtain ⟨v, hv, N, hN, hN1, hN75⟩ := (scaled_log_6_iff hT _ _).mp hsl
  simp only [List.cons.injEq, and_true] at hv
  have hNn : N = n := gen_pow_inj' (lt_trans hN (by norm_num)) (by omega) (hN1.symm.trans hng)
  subst hNn
  -- the windows
  have h0c : CellsAt rd (σ (.n 40)) [(digestScalars paramIv).1, (digestScalars paramIv).2, 0] := by
    rw [cellsAt_three, ← iv0_word, ← iv1_word, ← word_zero, ← c41, ← c42, ← c43]
    exact ⟨l41, l42, l43⟩
  have hsteps : ∀ j < w, L87Step rd (σ (.n 40)) (σ (.n 2)) (σ (.n 0)) (σ (.n 1)) (σ (.n 3))
      (σ (.n 4)) (σ (.n 6)) (coreProgram.Rel rd) (gen ^ j) := by
    intro j hj
    have hne : σ (.n 45) ≠ 0 := by
      rw [a45, c44, word_one, h18]
      intro h
      have := (gen_pow_eq_one_iff (by omega)).mp (e_add_eq_zero_iff.mp h).symm
      omega
    have hl := hloop hne
    rw [c46, word_one, ← pow_zero gen] at hl
    exact loop87_iters h18 (by omega) hl j hj
  have hW : ∀ q, ∃ offq : ℕ → ℕ, q < w → ∃ s0 s1 bs o0 o1 nxt csq,
      CellsAt rd (σ (.n 40) * gen ^ (4 * q)) [s0, s1, bs] ∧
      CellsAt rd (σ (.n 40) * gen ^ (4 * (q + 1))) [o0, o1, nxt] ∧ csq.length = 128 ∧
      ChildReads rd (σ (.n 0)) (σ (.n 1)) (σ (.n 2) * gen ^ (32 * q)) (σ (.n 3)) (σ (.n 4)) offq csq 32 ∧
      ChainCells (s0, s1) (blocksOf csq) (windowMd bs nxt) 32 (o0, o1) ∧
      nxt = eOfNat (2 ^ 11 * (q + 1)) := by
    intro q
    by_cases hq : q < w
    swap
    · exact ⟨fun _ => 0, fun h => absurd h hq⟩
    obtain ⟨s0, s1, bs, o0, o1, nxt, hslot, hwin, hstore⟩ := hsteps q hq
    obtain ⟨_, _, _, _, _, _, _, _, _, _, o0', o1', nxt', hargs, hrets, N', hN', hxq, hnxt, offq, csq,
      hlen, hRq, hch⟩ := child_window_fwd hm hT hwin
    simp only [List.cons.injEq, and_true] at hargs hrets
    obtain ⟨rfl, rfl, rfl, rfl, rfl, hmk, rfl, rfl, rfl, rfl⟩ := hargs
    obtain ⟨rfl, rfl, rfl⟩ := hrets
    rw [← pow_succ] at hxq
    have hNq : N' = q + 1 := (gen_pow_inj' (by omega) (lt_trans hN' (by norm_num)) hxq).symm
    subst hNq
    subst hmk
    simp only [pow32_eq] at hRq
    rw [pow4_eq _ q rfl] at hslot
    rw [← pow_succ, pow4_eq _ (q + 1) rfl] at hstore
    exact ⟨offq, fun _ => ⟨_, _, _, _, _, _, csq, hslot, hstore, hlen, hRq, hch, hnxt⟩⟩
  choose offW hW using hW
  -- the tail
  rw [← List.getD_eq_getElem _ "" ht] at htail
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hargs, hrets, offT, cst, hlent, hRt, hcht⟩ :=
    child_claims_tail_sound hm t ht32 _ _ htail
  simp only [List.cons.injEq, and_true] at hargs hrets
  obtain ⟨rfl, rfl, rfl, rfl, rfl, hmk, rfl, rfl⟩ := hargs
  obtain ⟨rfl, rfl⟩ := hrets
  rw [m55, m54, m53, m52, m51, m50, h18] at hmk
  have hmk' : σ (.n 2) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) *
      (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) *
      (gen ^ w * gen ^ w * (gen ^ w * gen ^ w))) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) *
      (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) *
      (gen ^ w * gen ^ w * (gen ^ w * gen ^ w))))) = σ (.n 2) * gen ^ (32 * w) := by ring
  rw [hmk'] at hmk
  rw [← hmk] at hRt
  -- the last claim
  rw [m63, c62] at rc61
  obtain ⟨eL, hx61, hLl⟩ := limit_of_rc hm rc61
  rw [m71, m70, hx61] at lmark
  rw [m69, m68, c67, hng,
    show gen ^ n * word 9223372036854775821 0 0 = gen ^ (n - 1) by
      rw [show gen ^ n = gen ^ (n - 1) * gen by rw [← pow_succ]; congr 1, mul_assoc,
        mul_comm gen, ginv_mul_gen, mul_one]] at lmark
  rw [m74, m73, m72, pow4_eq _ eL hx61] at l78 l79 l80 l81
  -- the indices and the cells
  set off : ℕ → ℕ := fun i => if i < 32 * w then offW (i / 32) (i % 32) else
    if i < 32 * w + t then offT (i - 32 * w) else eL with hoffdef
  set cs := csOf rd (σ (.n 0)) off (4 * n) with hcs
  have hwin := cwins_fwd (c := σ (.n 40)) (base := σ (.n 2)) (entries := σ (.n 0)) (cover := σ (.n 1))
    (origin := σ (.n 3)) (limit := σ (.n 4)) (len := 4 * n) (w := w) (off := off) (by omega) h0c
    (fun q hq => by
      obtain ⟨s0, s1, bs, o0, o1, nxt, csq, a, b, c, d, e, f⟩ := hW q hq
      refine ⟨s0, s1, bs, o0, o1, nxt, csq, a, b, c, ?_, e, f⟩
      refine (childReads_congr fun j hj => ?_).mp d
      simp only [hoffdef, show 32 * q + j < 32 * w by omega, ↓reduceIte,
        show (32 * q + j) / 32 = q by omega, show (32 * q + j) % 32 = j by omega])
  obtain ⟨hIw, hcanw, hRw⟩ := hwin w le_rfl
  have h49 : σ (.n 49) = σ (.n 40) * gen ^ (4 * w) := by rw [m49, m48, m47, pow4_eq _ w h18]
  rw [h49] at l56 l57 l58
  rw [cellsAt_three] at hIw
  have e56 := loadHolds_unique l56 hIw.1
  have e57 := loadHolds_unique l57 hIw.2.1
  have e58 := loadHolds_unique l58 hIw.2.2
  have hoT : ∀ j < t, off (32 * w + j) = offT j := fun j hj => by
    simp only [hoffdef, show ¬(32 * w + j < 32 * w) by omega, show 32 * w + j < 32 * w + t by omega,
      ↓reduceIte, Nat.add_sub_cancel_left]
  have hoL : off (n - 1) = eL := by
    simp only [hoffdef, show ¬(n - 1 < 32 * w) by omega, show ¬(n - 1 < 32 * w + t) by omega,
      ↓reduceIte]
  have hbt : ∀ j < t, blocksOf cst j = blocksOf cs (32 * w + j) := by
    intro j hj
    obtain ⟨-, -, hc⟩ := hRt j hj
    obtain ⟨a0, a1, a2, a3⟩ := block_of_entry hc
    rw [blocksOf_csOf (by omega), blocksOf_getD, a0, a1, a2, a3, hoT j hj]
  rw [e56, e57, e58, chainCells_prefix (k := 32 * w) hbt (fun j hj => baseMd_eq w j (by omega))] at hcht
  obtain ⟨hcant, hout⟩ := hcht
  rw [show 32 * w + t = n - 1 by omega] at hout
  have hlast : blocksOf cs (n - 1) = ![σ (.n 78), σ (.n 79), σ (.n 80), σ (.n 81)] := by
    obtain ⟨a0, a1, a2, a3⟩ := block_of_entry (cellsAt_four.mpr ⟨l78, l79, l80, l81⟩)
    rw [blocksOf_csOf (by omega), hoL, a0, a1, a2, a3]
  have h77 : σ (.n 77) = metadataCell (64 * n) true := by
    rw [a77, c76, hv, hN75, md_final_word, eOfNat_add_metadataCell, Nat.xor_zero]; rfl
  have hout1 := congrArg Prod.fst hout
  have hout2 := congrArg Prod.snd hout
  simp only at hout1 hout2
  rw [← hlast, h77, hout1, hout2] at hfin
  have hcanl := (compressCells_canonical hfin).1
  have hcan : ∀ j < n, ∀ r, IsCanonical128 (blocksOf cs j r) := by
    intro j hj
    rcases (show j < 32 * w ∨ 32 * w ≤ j ∧ j < 32 * w + t ∨ j = n - 1 by omega) with h | ⟨h1, h2⟩ | rfl
    · exact hcanw j h
    · have := hcant (j - 32 * w) (by omega)
      rwa [show 32 * w + (j - 32 * w) = j by omega] at this
    · exact hcanl
  have hlen : cs.length = 4 * n := length_csOf _ _ _ _
  refine ⟨_, _, _, _, _, _, _, σ (.n 82), σ (.n 83), rfl, hr.symm, n, hN, hng, off, cs, hlen, ?_,
    canonical_of_blocks hlen hcan, ?_, Or.inr ⟨σ (.n 40), fun q hq => (hwin q (by omega)).1⟩⟩
  · intro i hi
    rcases (show i < 32 * w ∨ 32 * w ≤ i ∧ i < 32 * w + t ∨ i = n - 1 by omega) with h | ⟨h1, h2⟩ | rfl
    · exact hRw i h
    · obtain ⟨hL, hs, hc⟩ := hRt (i - 32 * w) (by omega)
      rw [← hoT _ (by omega), show 32 * w + (i - 32 * w) = i by omega] at hL hs hc
      rw [mul_assoc, ← pow_add, show 32 * w + (i - 32 * w) = i by omega] at hs
      refine ⟨hL, hs, ?_⟩
      have hc' := entry_of_reads hc
      have e0 : cs.getD (4 * i) 0 = cellAt rd (σ (.n 0)) (4 * off i) := by
        simpa using csOf_getD (j := i) (r := 0) (off := off) (rd := rd) (entries := σ (.n 0))
          (by omega) (by omega)
      rw [e0, csOf_getD (by omega) (by omega), csOf_getD (by omega) (by omega),
        csOf_getD (by omega) (by omega)]
      exact hc'
    · refine ⟨by rw [hoL]; exact hLl, by rw [hoL]; exact lmark, ?_⟩
      have hc' := entry_of_reads (cellsAt_four.mpr ⟨l78, l79, l80, l81⟩)
      have e0 : cs.getD (4 * (n - 1)) 0 = cellAt rd (σ (.n 0)) (4 * off (n - 1)) := by
        simpa using csOf_getD (j := n - 1) (r := 0) (off := off) (rd := rd) (entries := σ (.n 0))
          (by omega) (by omega)
      rw [e0, csOf_getD (by omega) (by omega), csOf_getD (by omega) (by omega),
        csOf_getD (by omega) (by omega), hoL]
      exact hc'
  · rw [h82, h83]
    exact (final_iff hlen (by omega) hcanl).mp hfin

/-! ## Backward -/

/-- A slice of a child's list reads and marks as the list does, its marks shifted. -/
theorem childReads_slice {rd : Reader} {entries cover base origin limit : E} {off : ℕ → ℕ}
    {cs : List E} {n : ℕ} (hR : ChildReads rd entries cover base origin limit off cs n) (b m : ℕ)
    (hbm : b + m ≤ n) :
    ChildReads rd entries cover (base * gen ^ b) origin limit (fun k => off (b + k)) (sliceOf cs b m) m := by
  intro k hk
  obtain ⟨hL, hs, hc⟩ := hR (b + k) (by omega)
  refine ⟨hL, by rw [mul_assoc, ← pow_add]; exact hs, ?_⟩
  have e0 := sliceOf_getD cs b m (4 * k) (by omega)
  rw [e0, sliceOf_getD cs b m _ (by omega), sliceOf_getD cs b m _ (by omega),
    sliceOf_getD cs b m _ (by omega), show 4 * b + 4 * k = 4 * (b + k) by ring,
    show 4 * b + (4 * k + 1) = 4 * (b + k) + 1 by ring, show 4 * b + (4 * k + 2) = 4 * (b + k) + 2 by ring,
    show 4 * b + (4 * k + 3) = 4 * (b + k) + 3 by ring]
  exact hc

/-- The honest values of `child_claim_list_digest`, `n ≥ 1`. -/
noncomputable def cclList (entries cover base origin limit gsq c d0 d1 : E) (cs : List E) (eL L n w t : ℕ)
    (t1 t2 t3 t4 t5 t6 : E) : List E :=
  [entries, cover, base, origin, limit, gen ^ n, gsq, word 1 0 0, gen ^ n + word 1 0 0, 0, 0, 0, 0, 0,
   0, 0, d0, d1, gen ^ w, gen ^ t, word 2147483648 0 0, gen ^ (31 - t), t1, t2, word 55834575010 0 0,
   gen ^ (2047 - w), t3, t4, gen ^ w * gen ^ w, gen ^ w * gen ^ w * (gen ^ w * gen ^ w),
   gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)),
   gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) *
     (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w))),
   pow32 (gen ^ w), pow32 (gen ^ w) * gen ^ t, wInv, gen ^ n * wInv, word 2 0 0,
   gen ^ w * word 2 0 0, gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0),
   gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0) * (gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0)),
   c, word 13503953895743350343 11912009169889063794 0,
   word 11170449402626986623 6620516960021240235 0, word 0 0 0, word 1 0 0, word 1 0 0 + gen ^ w,
   word 1 0 0, gen ^ w * gen ^ w, gen ^ w * gen ^ w * (gen ^ w * gen ^ w),
   c * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)), gen ^ w * gen ^ w,
   gen ^ w * gen ^ w * (gen ^ w * gen ^ w),
   gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)),
   gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) *
     (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w))),
   pow32 (gen ^ w), base * pow32 (gen ^ w), (digestScalars (prefixDigest cs (32 * w))).1,
   (digestScalars (prefixDigest cs (32 * w))).2, eOfNat (2 ^ 11 * w),
   (digestScalars (prefixDigest cs (n - 1))).1, (digestScalars (prefixDigest cs (n - 1))).2,
   gen ^ eL, wInv, limit * wInv, gen ^ (L - 1 - eL), t5, t6, wInv, gen ^ n * wInv,
   base * (gen ^ n * wInv), origin * gen ^ eL, cover * (origin * gen ^ eL), gen ^ eL * gen ^ eL,
   gen ^ eL * gen ^ eL * (gen ^ eL * gen ^ eL), entries * (gen ^ eL * gen ^ eL * (gen ^ eL * gen ^ eL)),
   eOfNat (2 ^ 6 * n), word 0 4294967295 0, eOfNat (2 ^ 6 * n) + word 0 4294967295 0,
   cs.getD (4 * (n - 1) + 0) 0, cs.getD (4 * (n - 1) + 1) 0, cs.getD (4 * (n - 1) + 2) 0,
   cs.getD (4 * (n - 1) + 3) 0, d0, d1]

theorem child_claim_list_digest_bwd {rd : Reader} (hm : MemOk rd) {gsq : E}
    (hT : SquaresAt rd gsq) {entries cover base origin limit n_g : E} {rets : List E}
    (hL : ∃ L ≤ 2 ^ 16, limit = gen ^ L)
    (h : Meaning_child_claim_list_digest rd [entries, cover, base, origin, limit, n_g, gsq] rets) :
    coreProgram.Rel rd "child_claim_list_digest" [entries, cover, base, origin, limit, n_g, gsq]
      rets := by
  obtain ⟨_, _, _, _, _, _, _, d0, d1, hargs, rfl, n, hn, hng, off, cs, hlen, hR, hcan, hd, hscr⟩ := h
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
  rw [rel_of_find find_child_claim_list_digest]
  simp only [Fn.Sem, ccldBody, List.cons_append, List.nil_append, Stmt.HoldsList,
    Stmt.Holds, Atom.Holds, true_and, List.map_cons, List.map_nil]
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · rw [pow_zero] at hng
    subst hng
    rw [Nat.mul_zero, List.length_eq_zero_iff] at hlen
    subst hlen
    have h11 : (1 : E) + word 1 0 0 = 0 := by rw [word_one, e_add_self]
    refine ⟨listVal ([entries, cover, base, origin, limit, 1, gsq, word 1 0 0, 1 + word 1 0 0,
      word 0 0 0, word 0 0 0, word 0 0 0, word 0 0 0, word 13503953895743350343 11912009169889063794 0,
      word 11170449402626986623 6620516960021240235 0, word 0 4294967295 0, d0, d1] ++
      List.replicate 64 0 ++ [d0, d1]), rfl, rfl, rfl, ?_, fun _ => ?_, fun h => ?_⟩
    · show IsInK ((1 : E) + word 1 0 0)
      rw [h11, ← ofK_zero]; exact ofK_isInK _
    · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
      show CompressCells ![word 0 0 0, word 0 0 0, word 0 0 0, word 0 0 0]
        (word 13503953895743350343 11912009169889063794 0)
        (word 11170449402626986623 6620516960021240235 0) d0 d1 (word 0 4294967295 0)
      rw [word_zero, iv0_word, iv1_word, md_final_word]
      exact compressCells_empty_iff.mpr hd
    · exfalso; apply h; show (1 : E) + word 1 0 0 = 0; exact h11
  rcases hscr with h0 | ⟨c, hscr⟩
  · omega
  subst hng
  obtain ⟨L, hL16, hlim⟩ := hL
  subst hlim
  set w := (n - 1) / 32 with hw
  set t := (n - 1) % 32 with ht
  have hwt : n = 32 * w + t + 1 := by omega
  have ht32 : t < 32 := by omega
  have hw2 : w < 2048 := by omega
  have hoff : ∀ j < n, off j < L := fun j hj => by
    obtain ⟨⟨L', hL', hlim', ho⟩, -⟩ := hR j hj
    have := gen_pow_inj (a := L) (b := L') (by omega) (by omega) hlim'
    omega
  obtain ⟨t1, t2, l22, -, l23⟩ := rangeCheck_complete hm (e := t) (e' := 31 - t) (by omega) (by omega)
  obtain ⟨t3, t4, l26, -, l27⟩ := rangeCheck_complete hm (e := w) (e' := 2047 - w) (by omega) (by omega)
  obtain ⟨t5, t6, l65, -, l66⟩ := rangeCheck_complete hm (e := off (n - 1)) (e' := L - 1 - off (n - 1))
    (lt_of_lt_of_le (hoff _ (by omega)) hL16) (by omega)
  have hS := fun q (hq : q ≤ w) => cellsAt_three.mp (hscr q hq)
  obtain ⟨s00, s01, s02⟩ := hS 0 (by omega)
  obtain ⟨sw0, sw1, sw2⟩ := hS w le_rfl
  simp only [Nat.mul_zero, pow_zero, mul_one, eOfNat_zero] at s00 s01 s02
  rw [← pow4_eq _ w rfl] at sw0 sw1 sw2
  have hb := blocks_canonical hlen hcan
  -- the loop's iterations
  have hsteps : ∀ j < w, L87Step rd c base entries cover origin (gen ^ L) gsq (coreProgram.Rel rd) (gen ^ j) := by
    intro j hj
    have h0 := cellsAt_three.mp (hscr j (by omega))
    have h1 := hscr (j + 1) (by omega)
    rw [show 32 * (j + 1) = 32 * j + 32 by ring] at h1
    refine ⟨_, _, _, (digestScalars (prefixDigest cs (32 * j + 32))).1,
      (digestScalars (prefixDigest cs (32 * j + 32))).2, eOfNat (2 ^ 11 * (j + 1)),
      by rw [pow4_eq _ j rfl]; exact cellsAt_three.mpr h0, ?_,
      by rw [← pow_succ, pow4_eq _ (j + 1) rfl]; exact h1⟩
    refine child_window_bwd hm hT ⟨L, hL16, rfl⟩ ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl,
      j + 1, by omega, (pow_succ gen j).symm, rfl, fun k => off (32 * j + k), sliceOf cs (32 * j) 32,
      length_sliceOf _ _ _, ?_, ?_⟩
    · rw [pow32_eq]
      exact childReads_slice hR (32 * j) 32 (by omega)
    · refine (chainCells_prefix (blocksOf_sliceOf cs (32 * j) 32)
        (fun i hi => windowMd_eq j i hi)).mpr ⟨fun i hi r => ?_, rfl⟩
      exact hb _ (by omega) r
  have hlast : ![cs.getD (4 * (n - 1) + 0) 0, cs.getD (4 * (n - 1) + 1) 0,
      cs.getD (4 * (n - 1) + 2) 0, cs.getD (4 * (n - 1) + 3) 0] = blocksOf cs (n - 1) := by
    simp [blocksOf]
  have hmd : eOfNat (2 ^ 6 * n) + word 0 4294967295 0 = metadataCell (64 * n) true := by
    rw [md_final_word, eOfNat_add_metadataCell, Nat.xor_zero]; rfl
  have hinv : gen ^ n * wInv = gen ^ (n - 1) := by
    rw [show gen ^ n = gen ^ (n - 1) * gen by rw [← pow_succ]; congr 1; omega, mul_assoc, mul_comm gen,
      ginv_mul_gen, mul_one]
  obtain ⟨-, hmark, hcl⟩ := hR (n - 1) (by omega)
  refine ⟨listVal (cclList entries cover base origin (gen ^ L) gsq c d0 d1 cs (off (n - 1)) L n w t
    t1 t2 t3 t4 t5 t6), rfl, rfl, rfl, ?_, fun h => ?_, fun _ => ?_⟩
  · show IsInK (gen ^ n + word 1 0 0)
    rw [word_one, gen_pow_eq_ofK, ← ofK_one, ← ofK_add]; exact ofK_isInK _
  · exfalso
    have h' : gen ^ n + word 1 0 0 = 0 := h
    rw [word_one] at h'
    have := (gen_pow_eq_one_iff (by omega)).mp (e_add_eq_zero_iff.mp h')
    omega
  refine ⟨rfl, ⟨l22, ?_, l23⟩, rfl, ⟨l26, ?_, l27⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_,
    rfl, rfl, rfl, rfl, rfl, ?_, rfl, ?_, rfl, ?_, rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, ⟨l65, ?_, l66⟩, rfl, rfl, rfl, rfl, rfl, ?_, rfl,
    rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
  all_goals simp only [listVal, cclList, List.getD_cons_succ, List.getD_cons_zero]
  · rw [word_g31, ← pow_add]; congr 1; omega
  · rw [word_g2047, ← pow_add]; congr 1; omega
  · rw [pow32_eq, hinv, ← pow_add, show 32 * w + t = n - 1 by omega, e_add_self]
  · rw [iv0_word]; exact s00
  · rw [iv1_word]; exact s01
  · rw [word_zero]; exact s02
  · rw [word_one, gen_pow_eq_ofK, ← ofK_one, ← ofK_add]; exact ofK_isInK _
  · intro h
    rw [word_one, ← pow_zero gen]
    have hw0 : 0 < w := by
      rcases Nat.eq_zero_or_pos w with h0 | h0
      · exfalso; apply h; rw [h0, word_one, pow_zero, e_add_self]
      · exact h0
    exact (loop_iff (l87Step_mono rd c base entries cover origin (gen ^ L) gsq)
      (l87_step rd (gen ^ w) c base entries cover origin (gen ^ L) gsq) 0).mpr
      ⟨w, hw0, rfl, fun j h1 h2 he => by have := gen_pow_inj' (by omega) (by omega) he; omega,
        fun j _ h2 => hsteps j h2⟩
  · exact sw0
  · exact sw1
  · exact sw2
  · refine ⟨t, by simp [cctNames]; omega, gen_pow_eq_ofK t, ?_⟩
    rw [← List.getD_eq_getElem _ "" (by simp [cctNames]; omega)]
    refine child_claims_tail_complete hm t ht32 _ ⟨L, hL16, rfl⟩ ⟨_, _, _, _, _, _, _, _, _, _,
      rfl, rfl, fun k => off (32 * w + k), sliceOf cs (32 * w) t, length_sliceOf _ _ _, ?_, ?_⟩
    · rw [pow32_eq]
      exact childReads_slice hR (32 * w) t (by omega)
    · refine (chainCells_prefix (blocksOf_sliceOf cs (32 * w) t)
        (fun j hj => baseMd_eq w j (by omega))).mpr ⟨fun j hj r => hb _ (by omega) r, ?_⟩
      rw [show 32 * w + t = n - 1 by omega]
  · exact limit_mul_inv (hoff _ (by omega))
  · rw [hinv]; exact hmark
  · exact (scaled_log_6_iff hT _ _).mpr ⟨_, rfl, n, hn, rfl, rfl⟩
  all_goals try (rw [pow4_eq _ (off (n - 1)) rfl])
  · exact (cellsAt_four.mp hcl).1
  · exact (cellsAt_four.mp hcl).2.1
  · exact (cellsAt_four.mp hcl).2.2.1
  · exact (cellsAt_four.mp hcl).2.2.2
  · rw [hlast, hmd]
    exact (final_iff hlen (by omega) (hb (n - 1) (by omega))).mpr hd

/-- **`child_claim_list_digest`**: sound, and complete for a table of at most `2^16` slots. -/
theorem child_claim_list_digest_iff {rd : Reader} (hm : MemOk rd) {gsq : E} (hT : SquaresAt rd gsq)
    {entries cover base origin limit n_g : E} (rets : List E) (hL : ∃ L ≤ 2 ^ 16, limit = gen ^ L) :
    coreProgram.Rel rd "child_claim_list_digest" [entries, cover, base, origin, limit, n_g, gsq] rets ↔
      Meaning_child_claim_list_digest rd [entries, cover, base, origin, limit, n_g, gsq] rets :=
  ⟨child_claim_list_digest_fwd hm hT, child_claim_list_digest_bwd hm hT hL⟩


/-- Completeness, for every pointer `chain` of the windows' `HeapBuf` holding their honest
states. -/
theorem child_claim_list_digest_complete {rd : Reader} (hm : MemOk rd) {gsq : E}
    (hT : SquaresAt rd gsq) (chain : E) {entries cover base origin limit : E}
    (hL : ∃ L ≤ 2 ^ 16, limit = gen ^ L) {n : ℕ} (hn : n < 2 ^ 16) (off : ℕ → ℕ) {cs : List E}
    (hlen : cs.length = 4 * n) (hR : ChildReads rd entries cover base origin limit off cs n)
    (hcan : ∀ c ∈ cs, IsCanonical128 c) (hS : 0 < n → ChildScratch rd chain cs ((n - 1) / 32)) :
    coreProgram.Rel rd "child_claim_list_digest" [entries, cover, base, origin, limit, gen ^ n, gsq]
      [(digestScalars (blake2sBytes (cs.flatMap cellBytes))).1,
        (digestScalars (blake2sBytes (cs.flatMap cellBytes))).2] :=
  child_claim_list_digest_bwd hm hT hL ⟨entries, cover, base, origin, limit, _, gsq, _, _, rfl, rfl,
    n, hn, rfl, off, cs, hlen, hR, hcan, rfl, (Nat.eq_zero_or_pos n).imp id fun h => ⟨chain, hS h⟩⟩

end
end LeanVM.Guest.B1.Digest

namespace LeanVM.Guest.B1
export Digest (ChildScratch ChildReads Meaning_child_claim_list_digest child_claim_list_digest_iff
  child_claim_list_digest_fwd child_claim_list_digest_bwd child_claim_list_digest_complete)
end LeanVM.Guest.B1
