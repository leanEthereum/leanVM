/-
  LeanVM.Guest.B1.Tables.VerifyTablesReads

  `verify_tables`' reads from the stream: the five framework claims and the 104 column
  evaluations, absorbed in order, and the claims they pool.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesBase

/-!
# The reads (G:1600-1631, 1752-1758)

`verify_tables` reads five framework values (the memory's three limbs, the memory's and the
bytecode's final counters) while decomposing the bus, and the tables' 104 column evaluations
after the table sumcheck, each by `fs_next` from the cursor, each stored in `claim_pool` with its
point's length in `claim_cplen_g` (`vt_fresh`, `vt_evals`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Each column evaluation's first statement (`fs_next`). -/
def evStmt : List ℕ :=
  [4375, 4391, 4407, 4423, 4439, 4455, 4471, 4487, 4503, 4519, 4535, 4551, 4567, 4583,
    4599, 4863, 4879, 4895, 4911, 4927, 4943, 4959, 4975, 4991, 5007, 5023, 5039, 5055,
    5071, 5087, 5392, 5408, 5424, 5440, 5456, 5472, 5488, 5504, 5669, 5685, 5701, 5717,
    5733, 5749, 5765, 5781, 5797, 5813, 5829, 5845, 5861, 5877, 5893, 6192, 6208, 6224,
    6240, 6256, 6272, 6288, 6304, 6320, 6336, 6352, 6368, 6384, 6400, 6694, 6710, 6726,
    6742, 6758, 6774, 6790, 6806, 6822, 6838, 6854, 6870, 6886, 6902, 6918, 6934, 6950,
    6966, 6982, 6998, 7014, 7030, 7046, 7062, 7078, 7094, 7110, 7126, 7142, 7158, 7174,
    7190, 7206, 7222, 7238, 7254, 7270]

/-- Each column evaluation's word, by value number. -/
def evVal : List ℕ :=
  [4661, 4677, 4693, 4709, 4725, 4741, 4757, 4773, 4789, 4805, 4821, 4837, 4853, 4869,
    4885, 5149, 5165, 5181, 5197, 5213, 5229, 5245, 5261, 5277, 5293, 5309, 5325, 5341,
    5357, 5373, 5678, 5694, 5710, 5726, 5742, 5758, 5774, 5790, 5955, 5971, 5987, 6003,
    6019, 6035, 6051, 6067, 6083, 6099, 6115, 6131, 6147, 6163, 6179, 6478, 6494, 6510,
    6526, 6542, 6558, 6574, 6590, 6606, 6622, 6638, 6654, 6670, 6686, 6980, 6996, 7012,
    7028, 7044, 7060, 7076, 7092, 7108, 7124, 7140, 7156, 7172, 7188, 7204, 7220, 7236,
    7252, 7268, 7284, 7300, 7316, 7332, 7348, 7364, 7380, 7396, 7412, 7428, 7444, 7460,
    7476, 7492, 7508, 7524, 7540, 7556]

/-- Each column evaluation's table's `g^τ`, by value number. -/
def evTau : List ℕ :=
  [4660, 4660, 4660, 4660, 4660, 4660, 4660, 4660, 4660, 4660, 4660, 4660, 4660, 4660,
    4660, 5148, 5148, 5148, 5148, 5148, 5148, 5148, 5148, 5148, 5148, 5148, 5148, 5148,
    5148, 5148, 5677, 5677, 5677, 5677, 5677, 5677, 5677, 5677, 5954, 5954, 5954, 5954,
    5954, 5954, 5954, 5954, 5954, 5954, 5954, 5954, 5954, 5954, 5954, 6477, 6477, 6477,
    6477, 6477, 6477, 6477, 6477, 6477, 6477, 6477, 6477, 6477, 6477, 6979, 6979, 6979,
    6979, 6979, 6979, 6979, 6979, 6979, 6979, 6979, 6979, 6979, 6979, 6979, 6979, 6979,
    6979, 6979, 6979, 6979, 6979, 6979, 6979, 6979, 6979, 6979, 6979, 6979, 6979, 6979,
    6979, 6979, 6979, 6979, 6979, 6979]

/-- Column evaluation `j`'s statements: its `fs_next`, its copy, its pool and length stores. -/
def evT (j : ℕ) : List Stmt :=
  let v := evVal.getD j 0
  let s := if j = 0 then 4649 else evVal.getD (j - 1) 0 + 13
  fsNextT (.n s) (.n (s + 1)) (.n 4651) j v ++
    [.atom (.copy (.n (v + 15)) (.n v)), .atom (.load (.n v) (.n 13) (5 + j)),
      .atom (.load (.n (evTau.getD j 0)) (.n 14) (5 + j))]

theorem ev_blocks0 : ∀ j < 26, stmtsEqb (evT j) ((vtPre.drop (evStmt.getD j 0)).take 16) = true := by
  decide +kernel

theorem ev_blocks1 : ∀ j < 26, stmtsEqb (evT (26 + j))
    ((vtPre.drop (evStmt.getD (26 + j) 0)).take 16) = true := by
  decide +kernel

theorem ev_blocks2 : ∀ j < 26, stmtsEqb (evT (52 + j))
    ((vtPre.drop (evStmt.getD (52 + j) 0)).take 16) = true := by
  decide +kernel

theorem ev_blocks3 : ∀ j < 26, stmtsEqb (evT (78 + j))
    ((vtPre.drop (evStmt.getD (78 + j) 0)).take 16) = true := by
  decide +kernel

theorem ev_blocks : ∀ j < 104, stmtsEqb (evT j) ((vtPre.drop (evStmt.getD j 0)).take 16) = true := by
  intro j hj
  rcases Nat.lt_or_ge j 26 with h0 | h0
  · exact ev_blocks0 j h0
  rcases Nat.lt_or_ge j 52 with h1 | h1
  · have := ev_blocks1 (j - 26) (by omega); rwa [show 26 + (j - 26) = j by omega] at this
  rcases Nat.lt_or_ge j 78 with h2 | h2
  · have := ev_blocks2 (j - 52) (by omega); rwa [show 52 + (j - 52) = j by omega] at this
  · have := ev_blocks3 (j - 78) (by omega); rwa [show 78 + (j - 78) = j by omega] at this

/-- The column evaluations, by value number. -/
def evWords (σ : Val) : List E := (List.range 104).map fun j => σ (.n (evVal.getD j 0))

theorem obsAll_append_one' (cv : Digest) (xs : List E) (x : E) :
    obsAll cv (xs ++ [x]) = obsCv (obsAll cv xs) x := by
  simp [obsAll, List.foldl_append]

/-- **The 104 column evaluations** (G:1752-1758): from the state of `cv` at `(4649, 4650)`, the
words at the cursor `4651`, absorbed in order to the state at `(7569, 7570)`; each stored in
`claim_pool[5 + j]`, with its table's `g^τ` in `claim_cplen_g[5 + j]`; each copied to
`col_evals`. -/
theorem vt_evals {rd : Reader} {σ : Val} (h : VtHolds rd σ) {cv : Digest}
    (hcv : (σ (.n 4649), σ (.n 4650)) = digestScalars cv) :
    ReadsAt rd (σ (.n 4651)) (evWords σ) ∧
      (σ (.n 7569), σ (.n 7570)) = digestScalars (obsAll cv (evWords σ)) ∧
      ∀ j < 104, LoadHolds rd (σ (.n 13)) (5 + j) (σ (.n (evVal.getD j 0))) ∧
        LoadHolds rd (σ (.n 14)) (5 + j) (σ (.n (evTau.getD j 0))) ∧
        σ (.n (evVal.getD j 0 + 15)) = σ (.n (evVal.getD j 0)) := by
  have hb : ∀ j < 104, (LoadHolds rd (σ (.n 4651)) j (σ (.n (evVal.getD j 0))) ∧
      ∃ c, (σ (.n (if j = 0 then 4649 else evVal.getD (j - 1) 0 + 13)),
        σ (.n ((if j = 0 then 4649 else evVal.getD (j - 1) 0 + 13) + 1))) = digestScalars c ∧
        (σ (.n (evVal.getD j 0 + 13)), σ (.n (evVal.getD j 0 + 14))) =
          digestScalars (obsCv c (σ (.n (evVal.getD j 0)))))
      ∧ σ (.n (evVal.getD j 0 + 15)) = σ (.n (evVal.getD j 0)) ∧
      LoadHolds rd (σ (.n 13)) (5 + j) (σ (.n (evVal.getD j 0))) ∧
      LoadHolds rd (σ (.n 14)) (5 + j) (σ (.n (evTau.getD j 0))) := by
    intro j hj
    have hs := h.slice _ _ (ev_blocks j hj)
    obtain ⟨k, hs⟩ := hs
    rw [evT, holdsList_append] at hs
    rw [holds_fsNextT] at hs
    obtain ⟨⟨hl, c, hc, hv⟩, hrest⟩ := hs
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hrest
    refine ⟨⟨hl, c, hc, ?_⟩, hrest⟩
    have h12 := hv 12 (by omega) (by omega)
    have h13 := hv 13 (by omega) (by omega)
    rw [show evVal.getD j 0 + 1 + 12 = evVal.getD j 0 + 13 by omega] at h12
    rw [show evVal.getD j 0 + 1 + 13 = evVal.getD j 0 + 14 by omega] at h13
    rw [h12, h13, fsVals, fsVals, absorbCv_one]
  have hchain : ∀ j ≤ 104, (σ (.n (if j = 0 then 4649 else evVal.getD (j - 1) 0 + 13)),
      σ (.n ((if j = 0 then 4649 else evVal.getD (j - 1) 0 + 13) + 1))) =
        digestScalars (obsAll cv ((evWords σ).take j)) := by
    intro j hj
    induction j with
    | zero => simpa [obsAll] using hcv
    | succ j ih =>
      obtain ⟨⟨-, c, hc, hout⟩, -⟩ := hb j (by omega)
      rw [ih (by omega)] at hc
      rw [← digestScalars_injective hc] at hout
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [List.take_add_one, List.getElem?_eq_getElem (by simp [evWords]; omega), Option.toList_some,
        obsAll_append_one']
      simpa [evWords] using hout
  refine ⟨fun j hj => ?_, ?_, fun j hj => ⟨(hb j hj).2.2.1, (hb j hj).2.2.2, (hb j hj).2.1⟩⟩
  · have hj' : j < 104 := by simpa [evWords] using hj
    simpa [evWords] using (hb j hj').1.1
  · have := hchain 104 le_rfl
    simp only [OfNat.ofNat_ne_zero, ↓reduceIte] at this
    rw [List.take_of_length_le (by simp [evWords])] at this
    exact this

end
end LeanVM.Guest.B1.VerifySub
