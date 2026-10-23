/-
  LeanVM.Guest.B1.Digest.ClaimWindow

  B1 for `claims_window` (G:2726-2744; TRIAGE #60): one window of a claim list's hash.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimTail
public import LeanVM.Guest.B1.Digest.ScaledLog

/-!
# `claims_window`

`claims_window(state_0, state_1, base, entries_ptr, x_q, g_squares)`: 32 claims read at
`entries_ptr`, compressed in sequence from the state cells, block `j < 31` under
`base + E(64·(j + 1))` and the last under the next window's base, `nxt = E(2^11 · N)` for
`x_q·g = g^N` (`scaled_log__L11`); it returns the state and `nxt`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- The metadata cells of a window: `baseMd base` then `nxt`. -/
def windowMd (base nxt : E) (j : ℕ) : E := if j < 31 then baseMd base j else nxt

/-- **`claims_window`**: `x_q·g = g^N`, `N < 2^16`, `nxt = E(2^11·N)`, and the 32 claims at
`ptr` chained from the state under `windowMd base nxt`. -/
def Meaning_claims_window (rd : Reader) (args rets : List E) : Prop :=
  ∃ s0 s1 base ptr xq gsq o0 o1 nxt, args = [s0, s1, base, ptr, xq, gsq] ∧ rets = [o0, o1, nxt] ∧
    ∃ N < 2 ^ 16, xq * gen = gen ^ N ∧ nxt = eOfNat (2 ^ 11 * N) ∧ ∃ cs : List E,
      cs.length = 128 ∧ CellsAt rd ptr cs ∧ ChainCells (s0, s1) (blocksOf cs) (windowMd base nxt) 32 (o0, o1)

/-! ## The template -/

/-- Block `j < 31`. -/
def cwBlk (j : ℕ) : List Atom :=
  [.hint (.witness "claims" (.heap (.n 3) (4 * j) 4)),
   .load (.n (11 + 8 * j)) (.n 3) (4 * j), .load (.n (12 + 8 * j)) (.n 3) (4 * j + 1),
   .load (.n (13 + 8 * j)) (.n 3) (4 * j + 2), .load (.n (14 + 8 * j)) (.n 3) (4 * j + 3),
   .const (.n (15 + 8 * j)) (word (64 * (j + 1)) 0 0), .add (.n (16 + 8 * j)) (.n 2) (.n (15 + 8 * j)),
   .blake2s (.n (11 + 8 * j)) (.n (12 + 8 * j)) (.n (13 + 8 * j)) (.n (14 + 8 * j)) (.n (9 + 8 * j))
     (.n (10 + 8 * j)) (.n (9 + 8 * (j + 1))) (.n (10 + 8 * (j + 1))) (.n (16 + 8 * j))]

/-- `claims_window`'s body. -/
def cwBody : List Stmt :=
  ([.const (.n 6) (word 2 0 0), .mul (.n 7) (.n 4) (.n 6)] : List Atom).map .atom ++
  [.call "scaled_log__L11" [.n 7, .n 5] [.n 8]] ++
  (([.copy (.n 9) (.n 0), .copy (.n 10) (.n 1)] : List Atom) ++ (List.range 31).flatMap cwBlk ++
    ([.hint (.witness "claims" (.heap (.n 3) 124 4)), .load (.n 259) (.n 3) 124,
      .load (.n 260) (.n 3) 125, .load (.n 261) (.n 3) 126, .load (.n 262) (.n 3) 127,
      .blake2s (.n 259) (.n 260) (.n 261) (.n 262) (.n 257) (.n 258) (.n 263) (.n 264) (.n 8),
      .copy (.n 265) (.n 263), .copy (.n 266) (.n 264), .copy (.n 267) (.n 8)] : List Atom)).map .atom ++
  [.ret [.n 265, .n 266, .n 267]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem find_claims_window : coreProgram.find? "claims_window" =
    some ⟨"claims_window", [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5], cwBody⟩ :=
  Program.find?_of_indexOf? (j := 19) (by decide +kernel) rfl

/-! ## The relation -/

section
variable (s0 s1 base ptr xq gsq nxt : E) (cs : List E) (h : Digest)

/-- The state after `j` blocks. -/
def cwS (j : ℕ) : E × E := digestScalars (chainRun h (blocksOf cs) (windowMd base nxt) j)

/-- The honest values of `claims_window`. -/
def cwVals (i : ℕ) : E :=
  if i < 9 then [s0, s1, base, ptr, xq, gsq, word 2 0 0, xq * word 2 0 0, nxt].getD i 0 else
  if (i - 9) % 8 = 0 then (cwS base nxt cs h ((i - 9) / 8)).1 else
  if (i - 9) % 8 = 1 then (cwS base nxt cs h ((i - 9) / 8)).2 else
  if (i - 9) % 8 = 6 then
    (if (i - 9) / 8 < 31 then word (64 * ((i - 9) / 8 + 1)) 0 0 else (cwS base nxt cs h 32).1) else
  if (i - 9) % 8 = 7 then
    (if (i - 9) / 8 < 31 then baseMd base ((i - 9) / 8) else (cwS base nxt cs h 32).2) else
  if (i - 9) / 8 < 32 then cs.getD (4 * ((i - 9) / 8) + ((i - 9) % 8 - 2)) 0 else nxt

theorem cwVals_st (j : ℕ) :
    cwVals s0 s1 base ptr xq gsq nxt cs h (9 + 8 * j) = (cwS base nxt cs h j).1 ∧
      cwVals s0 s1 base ptr xq gsq nxt cs h (10 + 8 * j) = (cwS base nxt cs h j).2 := by
  constructor
  · simp only [cwVals, show ¬(9 + 8 * j < 9) by omega, show (9 + 8 * j - 9) % 8 = 0 by omega,
      show (9 + 8 * j - 9) / 8 = j by omega, ↓reduceIte]
  · simp only [cwVals, show ¬(10 + 8 * j < 9) by omega, show (10 + 8 * j - 9) % 8 = 1 by omega,
      show (10 + 8 * j - 9) / 8 = j by omega, ↓reduceIte, one_ne_zero]

theorem cwVals_cell (j r : ℕ) (hj : j < 32) (hr : r < 4) :
    cwVals s0 s1 base ptr xq gsq nxt cs h (11 + 8 * j + r) = cs.getD (4 * j + r) 0 := by
  simp only [cwVals, show ¬(11 + 8 * j + r < 9) by omega,
    show (11 + 8 * j + r - 9) % 8 = r + 2 by omega, show (11 + 8 * j + r - 9) / 8 = j by omega,
    show r + 2 ≠ 0 by omega, show r + 2 ≠ 1 by omega, show r + 2 ≠ 6 by omega,
    show r + 2 ≠ 7 by omega, hj, ↓reduceIte, Nat.add_sub_cancel]

theorem cwVals_md (j : ℕ) (hj : j < 31) :
    cwVals s0 s1 base ptr xq gsq nxt cs h (15 + 8 * j) = word (64 * (j + 1)) 0 0 ∧
      cwVals s0 s1 base ptr xq gsq nxt cs h (16 + 8 * j) = baseMd base j := by
  constructor
  · simp only [cwVals, show ¬(15 + 8 * j < 9) by omega, show (15 + 8 * j - 9) % 8 = 6 by omega,
      show (15 + 8 * j - 9) / 8 = j by omega, hj, ↓reduceIte]
    simp
  · simp only [cwVals, show ¬(16 + 8 * j < 9) by omega, show (16 + 8 * j - 9) % 8 = 7 by omega,
      show (16 + 8 * j - 9) / 8 = j by omega, hj, ↓reduceIte]
    simp

theorem cwVals_tail :
    cwVals s0 s1 base ptr xq gsq nxt cs h 263 = (cwS base nxt cs h 32).1 ∧
      cwVals s0 s1 base ptr xq gsq nxt cs h 264 = (cwS base nxt cs h 32).2 ∧
      cwVals s0 s1 base ptr xq gsq nxt cs h 267 = nxt := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [cwVals]

end

theorem claims_window_iff {rd : Reader} {gsq : E} (hT : SquaresAt rd gsq)
    (s0 s1 base ptr xq : E) (rets : List E) :
    coreProgram.Rel rd "claims_window" [s0, s1, base, ptr, xq, gsq] rets ↔
      Meaning_claims_window rd [s0, s1, base, ptr, xq, gsq] rets := by
  rw [rel_of_find find_claims_window]
  simp only [Fn.Sem, cwBody, holdsList_atoms, List.cons_append, List.nil_append,
    Stmt.HoldsList, Stmt.Holds, List.forall_mem_append, forall_mem_flatMap_range,
    cwBlk, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true, true_and, List.map_cons,
    List.map_nil, Meaning_claims_window]
  constructor
  · rintro ⟨σ, hp, c6, m7, hcall, c9, c10, ⟨hblk, l0, l1, l2, l3, hc, h265, h266, h267⟩, hr⟩
    simp only [List.cons.injEq, and_true] at hp
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hp
    obtain ⟨v, hv, N, hN, h7, h8⟩ := (scaled_log_11_iff hT _ _).mp hcall
    simp only [List.cons.injEq, and_true] at hv
    set cs := (List.range (4 * 32)).map (fun i => σ (.n (11 + 8 * (i / 4) + i % 4))) with hcsdef
    have hcs : ∀ j r, j < 32 → r < 4 → cs.getD (4 * j + r) 0 = σ (.n (11 + 8 * j + r)) :=
      cs_getD' 11 32 (fun i => σ (.n i))
    have hch := chainCells_of_steps (n := 32)
      (blocks := fun j => ![σ (.n (11 + 8 * j)), σ (.n (12 + 8 * j)), σ (.n (13 + 8 * j)),
        σ (.n (14 + 8 * j))]) (md := fun j => if j < 31 then σ (.n (16 + 8 * j)) else σ (.n 8))
      (st := fun j => if j = 32 then (σ (.n 263), σ (.n 264)) else (σ (.n (9 + 8 * j)), σ (.n (10 + 8 * j))))
      (fun j hj => by
        rcases (show j < 31 ∨ j = 31 by omega) with h | rfl
        · simp only [show j ≠ 32 by omega, show j + 1 ≠ 32 by omega, h, ↓reduceIte]
          exact (hblk j h).2.2.2.2.2.2
        · exact hc)
    simp only [show (0 : ℕ) ≠ 32 by omega, ↓reduceIte, Nat.mul_zero, Nat.add_zero] at hch
    refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 265), σ (.n 266),
      σ (.n 267), rfl, hr.symm, N, hN, by rw [← h7, m7, c6, word_eq_eOfNat]; rfl,
      by rw [h267, hv, h8], cs, by simp [cs], ?_, ?_⟩
    · intro i hi
      have hi' : i < 128 := by simpa [cs] using hi
      obtain ⟨j, r, hr4, rfl⟩ : ∃ j r, r < 4 ∧ i = 4 * j + r := ⟨i / 4, i % 4, by omega, by omega⟩
      rw [← List.getD_eq_getElem _ 0 hi, hcs j r (by omega) hr4]
      rcases (show j < 31 ∨ j = 31 by omega) with hj | rfl
      · obtain ⟨m0, m1, m2, m3, -⟩ := hblk j hj
        interval_cases r
        · simpa using m0
        · rw [show 11 + 8 * j + 1 = 12 + 8 * j by omega]; exact m1
        · rw [show 11 + 8 * j + 2 = 13 + 8 * j by omega]; exact m2
        · rw [show 11 + 8 * j + 3 = 14 + 8 * j by omega]; exact m3
      · interval_cases r
        exacts [l0, l1, l2, l3]
    · rw [← c9, ← c10, h265, h266, h267]
      rw [chainCells_congr (b' := fun j => ![σ (.n (11 + 8 * j)), σ (.n (12 + 8 * j)),
          σ (.n (13 + 8 * j)), σ (.n (14 + 8 * j))])
          (md' := fun j => if j < 31 then σ (.n (16 + 8 * j)) else σ (.n 8)) (fun j hj => ?_)
          (fun j hj => ?_)]
      · exact hch
      · have e0 := hcs j 0 hj (by omega)
        have e1 := hcs j 1 hj (by omega)
        have e2 := hcs j 2 hj (by omega)
        have e3 := hcs j 3 hj (by omega)
        rw [Nat.add_zero, Nat.add_zero] at e0
        rw [show 11 + 8 * j + 1 = 12 + 8 * j by omega] at e1
        rw [show 11 + 8 * j + 2 = 13 + 8 * j by omega] at e2
        rw [show 11 + 8 * j + 3 = 14 + 8 * j by omega] at e3
        simp only [blocksOf, e0, e1, e2, e3]
      · unfold windowMd
        split_ifs with h
        · rw [baseMd, (hblk j h).2.2.2.2.2.1, (hblk j h).2.2.2.2.1, word_md]
        · rfl
  · rintro ⟨s0', s1', base', ptr', xq', gsq', o0, o1, nxt, hargs, rfl, N, hN, hxq, hnxt, cs, hlen,
      hcells, hch⟩
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
    rcases hch with ⟨h0, -⟩ | ⟨-, h, hst, hcan, hout⟩
    · omega
    have est := cwVals_st s0 s1 base ptr xq gsq nxt cs h
    have ecl := cwVals_cell s0 s1 base ptr xq gsq nxt cs h
    have emd := cwVals_md s0 s1 base ptr xq gsq nxt cs h
    obtain ⟨t263, t264, t267⟩ := cwVals_tail s0 s1 base ptr xq gsq nxt cs h
    have hS0 : cwS base nxt cs h 0 = (s0, s1) := by rw [cwS, chainRun, ← hst]
    have hl : ∀ i < 128, LoadHolds rd ptr i (cs.getD i 0) := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact hcells _ (by omega)
    have hstep := steps_of_chainCells (h := h) hcan
    refine ⟨fun v => cwVals s0 s1 base ptr xq gsq nxt cs h v.idx, rfl, rfl, rfl, ?_, ?_, ?_,
      ⟨fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact (scaled_log_11_iff hT _ _).mpr ⟨nxt, rfl, N, hN,
        by show xq * word 2 0 0 = gen ^ N; rw [word_eq_eOfNat]; exact hxq, hnxt⟩
    · show cwVals s0 s1 base ptr xq gsq nxt cs h (9 + 8 * 0) = _
      rw [(est 0).1, hS0]; rfl
    · show cwVals s0 s1 base ptr xq gsq nxt cs h (10 + 8 * 0) = _
      rw [(est 0).2, hS0]; rfl
    · dsimp only
      rw [show cwVals s0 s1 base ptr xq gsq nxt cs h 3 = ptr from rfl,
        show cwVals s0 s1 base ptr xq gsq nxt cs h 2 = base from rfl,
        show 11 + 8 * j = 11 + 8 * j + 0 by rfl, show 12 + 8 * j = 11 + 8 * j + 1 by omega,
        show 13 + 8 * j = 11 + 8 * j + 2 by omega, show 14 + 8 * j = 11 + 8 * j + 3 by omega,
        ecl j 0 (by omega) (by omega), ecl j 1 (by omega) (by omega), ecl j 2 (by omega) (by omega),
        ecl j 3 (by omega) (by omega), (emd j hj).1, (emd j hj).2, (est j).1, (est j).2,
        (est (j + 1)).1, (est (j + 1)).2]
      refine ⟨by simpa using hl (4 * j) (by omega), hl _ (by omega), hl _ (by omega),
        hl _ (by omega), rfl, by rw [baseMd, word_md], ?_⟩
      have := hstep j (by omega)
      rwa [windowMd, ite_pos' hj] at this
    · exact hl 124 (by omega)
    · exact hl 125 (by omega)
    · exact hl 126 (by omega)
    · exact hl 127 (by omega)
    · show CompressCells ![cwVals s0 s1 base ptr xq gsq nxt cs h (11 + 8 * 31 + 0),
        cwVals s0 s1 base ptr xq gsq nxt cs h (11 + 8 * 31 + 1),
        cwVals s0 s1 base ptr xq gsq nxt cs h (11 + 8 * 31 + 2),
        cwVals s0 s1 base ptr xq gsq nxt cs h (11 + 8 * 31 + 3)]
        (cwVals s0 s1 base ptr xq gsq nxt cs h (9 + 8 * 31))
        (cwVals s0 s1 base ptr xq gsq nxt cs h (10 + 8 * 31))
        (cwVals s0 s1 base ptr xq gsq nxt cs h 263) (cwVals s0 s1 base ptr xq gsq nxt cs h 264)
        (cwVals s0 s1 base ptr xq gsq nxt cs h 8)
      rw [ecl 31 0 (by omega) (by omega), ecl 31 1 (by omega) (by omega),
        ecl 31 2 (by omega) (by omega), ecl 31 3 (by omega) (by omega), (est 31).1, (est 31).2,
        t263, t264, show cwVals s0 s1 base ptr xq gsq nxt cs h 8 = nxt from rfl]
      have := hstep 31 (by omega)
      rwa [windowMd, ite_neg' (by omega)] at this
    · show cwVals s0 s1 base ptr xq gsq nxt cs h (9 + 8 * 32) =
        cwVals s0 s1 base ptr xq gsq nxt cs h 263
      rw [(est 32).1, t263]
    · show cwVals s0 s1 base ptr xq gsq nxt cs h (10 + 8 * 32) =
        cwVals s0 s1 base ptr xq gsq nxt cs h 264
      rw [(est 32).2, t264]
    · show cwVals s0 s1 base ptr xq gsq nxt cs h 267 = cwVals s0 s1 base ptr xq gsq nxt cs h 8
      rw [t267]; rfl
    · show [cwVals s0 s1 base ptr xq gsq nxt cs h (9 + 8 * 32),
        cwVals s0 s1 base ptr xq gsq nxt cs h (10 + 8 * 32),
        cwVals s0 s1 base ptr xq gsq nxt cs h 267] = _
      rw [(est 32).1, (est 32).2, t267, cwS, ← hout]

end
end LeanVM.Guest.B1.Digest
