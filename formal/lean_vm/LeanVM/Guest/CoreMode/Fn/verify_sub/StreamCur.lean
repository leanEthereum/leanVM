/-
  LeanVM.Guest.CoreMode.Fn.verify_sub.StreamCur

  `verify_sub`'s cursor through the link and the Keccak reduction, on a run of its body: each callee's returned cursor
  its argument times `g^k`, `k` the words its rounds read.
-/

module

public import LeanVM.Guest.B1.VerifySub.PhLink
public import LeanVM.Guest.B1.VerifySub.Keccak
public import LeanVM.Guest.B1.VerifySub.PhOpen
import Mathlib.Tactic.IntervalCases

/-!
# The cursor, phase by phase

* `chain_cur`: a chain of `l` rounds of `nt` tail coefficients and `bits` of grind advances the cursor by
  `l·(nt + 1 + [bits ≠ 0])` words.
* `vs_c580`: `opening_message` leaves the cursor at `stream·g^13`.
* `vs_c772`: `link_rounds` leaves it `2w` words further, `g_w = g^w` (value `409`).
* `vs_c1076`: `link_row_side`'s arm `j` (`σ1070 = g^j`, `j < 4`) leaves `cursor@3` at `σ772·g·g^(n·S + 6·S')`,
  `g_n = g^n` (value `408`), `(S, S') = rowStrides j`.
* `vs_c2920`: `cursor@4 = cursor@3·g^(144 + k)` (`verify_keccak`'s words, `phKeccak`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Link
open LeanVM.Guest.B1.VerifySub LeanVM.Protocol.Verifier

@[expose] public section

/-- A round's words past its tail: its first coefficient and, when it grinds, the nonce. -/
def gw (bits : ℕ) : ℕ := if bits = 0 then 0 else 1

/-- `link_row_side`'s arm `j`: the words of a row round and of a pointer-column round. -/
def rowStrides : List (ℕ × ℕ) := [(8, 7), (10, 8), (11, 10), (12, 11)]

end

public section

theorem grindWords_length (bits : ℕ) (n : E) : (grindWords bits n).length = gw bits := by
  unfold grindWords gw; split <;> rfl

/-- **A chain of rounds advances the cursor** by its words. -/
theorem chain_cur {rd : Reader} {nt bits : ℕ} : ∀ {st : RSt} {l : List (E × RSt)}, RoundChain rd nt bits st l →
    (chainLast st l).cur = st.cur * gen ^ (l.length * (nt + 1 + gw bits))
  | st, [], _ => by simp [chainLast]
  | st, (y, st') :: l, ⟨⟨c0, tail, n, _, _, _, _, hcur, _⟩, hc⟩ => by
    show (chainLast st' l).cur = _
    rw [chain_cur hc, hcur, grindWords_length, mul_assoc, ← pow_add]
    congr 2
    simp only [List.length_cons]
    ring

/-- The cursor a chain's cells return. -/
theorem cells_cur {st : RSt} (h : st.cap.length = 5) {rets : List E} (hr : rets = st.cells) :
    rets.getD 5 0 = st.cur := by
  obtain ⟨a, b, c, d, e, u, v, hc, hst⟩ := cells_eq_seven h
  rw [hr, hc, hst]
  rfl

/-- **`link_row_side`'s returned cursor**: past its `n` row rounds and `6` pointer-column rounds. -/
theorem rowSide_cur {rd : Reader} {nt1 b1 nt2 b2 : ℕ} {f0 f1 f2 f3 f4 cur cl chi qp gn tabs : E} {rets : List E}
    (hw : WinTabs rd tabs) (hM : MeaningLRS nt1 b1 nt2 b2 rd [f0, f1, f2, f3, f4, cur, cl, chi, qp, gn, tabs] rets) :
    ∃ n < 64, gn = gen ^ n ∧ rets.getD 5 0 = cur * gen ^ (n * (nt1 + 1 + gw b1) + 6 * (nt2 + 1 + gw b2)) := by
  simp only [MeaningLRS] at hM
  obtain ⟨n, hn, hgn, hch⟩ := hM
  obtain ⟨l1, l2, hl1, hl2, hc1, hc2, -, -, hret⟩ := hch (fun _ ↦ hw)
  refine ⟨n, hn, hgn, ?_⟩
  rw [cells_cur (chainLast_cap_length (chainLast_cap_length rfl hc1) hc2) hret, chain_cur hc2, chain_cur hc1,
    hl1, hl2, mul_assoc, ← pow_add]

variable {bytecode : List K} {κ : ℕ} {L : MemoryImage κ} {C : CallRel} {V : FrameMap} {σ : Val} {rets : List E}

/-- **Past the out-of-domain value**: `opening_message` leaves the cursor at `stream·g^13`. -/
theorem vs_c580 (R : VsRun bytecode L C V σ rets) : σ (.n 580) = σ (.n 55) * gen ^ 13 := by
  obtain ⟨c, hc, -⟩ := R.shapeOk.chunks
  obtain ⟨-, -, -, h, -⟩ := R.linkFront hc
  exact h

/-- **Past the index side's rounds**: `link_rounds` reads two words a round, `g_w = g^w` rounds. -/
theorem vs_c772 (R : VsRun bytecode L C V σ rets) :
    ∃ w < 64, σ (.n 409) = gen ^ w ∧ σ (.n 772) = σ (.n 580) * gen ^ (2 * w) := by
  have hI := R.slice vsLkIdxT_eq
  simp only [vsLkIdxT, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hI
  obtain ⟨-, -, hlr, -⟩ := hI
  have M := link_rounds_L1_L0_sound L.read (fun h ↦ absurd rfl h) _ _ (R.hle _ _ _ hlr)
  simp only [MeaningLR] at M
  obtain ⟨cnt, hcnt, hcg, hch⟩ := M
  obtain ⟨l, hll, hchain, -, hret⟩ := hch (fun h ↦ absurd rfl h)
  have e := cells_cur (chainLast_cap_length rfl hchain) hret
  rw [chain_cur hchain, hll] at e
  refine ⟨cnt, hcnt, hcg, ?_⟩
  rw [show (2 : ℕ) * cnt = cnt * (1 + 1 + gw 0) by simp [gw]; ring]
  exact e

/-- **Past the row side**: `link_row_side`'s arm `j` reads `n·S + 6·S'` words past `σ772·g`. -/
theorem vs_c1076 (R : VsRun bytecode L C V σ rets) :
    ∃ j < 4, ∃ n < 64, σ (.n 1070) = ofK (addressOfIndex j) ∧ σ (.n 408) = gen ^ n ∧
      σ (.n 1076) = σ (.n 772) * gen * gen ^ (n * (rowStrides.getD j (0, 0)).1 + 6 * (rowStrides.getD j (0, 0)).2) := by
  obtain ⟨-, hwin, h11⟩ := R.pre
  have hgc : GcSound1 L.read := gcSound1_image R.hκ h11 L
  have hW := R.slice vsLkRowT_eq
  simp only [vsLkRowT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hW
  obtain ⟨w0, w1, w2, w3, -, -, ⟨j, hj, hsel, hcall⟩, -⟩ := hW
  have hj4 : j < 4 := by simpa using hj
  have hwt : WinTabs L.read (σ (.n 1068)) := by
    rw [w3, w2, word_winTab]; exact winTabs_of_expWinTab hwin
  have hcur : σ (.n 1066) = σ (.n 772) * gen := by rw [w1, w0, word_gen]
  refine ⟨j, hj4, ?_⟩
  interval_cases j
  · obtain ⟨n, hn, hgn, h⟩ := rowSide_cur hwt (link_row_side_L6_sound L.read hgc _ _ (R.hle _ _ _ hcall))
    exact ⟨n, by omega, hsel, hgn, by rw [← hcur]; exact h⟩
  · obtain ⟨n, hn, hgn, h⟩ := rowSide_cur hwt (link_row_side_L7_sound L.read hgc _ _ (R.hle _ _ _ hcall))
    exact ⟨n, by omega, hsel, hgn, by rw [← hcur]; exact h⟩
  · obtain ⟨n, hn, hgn, h⟩ := rowSide_cur hwt (link_row_side_L8_sound L.read hgc _ _ (R.hle _ _ _ hcall))
    exact ⟨n, by omega, hsel, hgn, by rw [← hcur]; exact h⟩
  · obtain ⟨n, hn, hgn, h⟩ := rowSide_cur hwt (link_row_side_L9_sound L.read hgc _ _ (R.hle _ _ _ hcall))
    exact ⟨n, by omega, hsel, hgn, by rw [← hcur]; exact h⟩

/-- **Past the Keccak reduction**: `cursor@4 = cursor@3·g^(144 + k)`. -/
theorem vs_c2920 (R : VsRun bytecode L C V σ rets) :
    ∃ k < 2 ^ 33, σ (.n 2920) = σ (.n 1076) * gen ^ (144 + k) := by
  obtain ⟨xs, link, s, -, -, -, -, hLF⟩ := phLink _ _ _ _ _ _ R
  obtain ⟨ys, -, -, -, -, hys, hR, -⟩ := phKeccak _ _ _ _ _ _ R link hLF
  have hK := R.slice vsKeccakT_eq
  simp only [vsKeccakT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hK
  obtain ⟨-, -, k2909, k2910, -⟩ := hK
  refine ⟨ys.length, readsAt_length_lt R.hκ L hys, ?_⟩
  have e : vsCurK σ = σ (.n 1076) * gen ^ 144 := by
    show σ (.n 2910) = _
    rw [k2910, k2909, word_g144]
  show vsCurR σ = _
  rw [hR, e, mul_assoc, ← pow_add]

end

end LeanVM.Guest.EndExec
