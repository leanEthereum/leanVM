/-
  LeanVM.Guest.B1.Eq.RsRowsAll

  B1 for `rs_eq_rows_all__L{n}`, `n ≤ 8`: the telescoped ring-switch rows, every partial product kept.
-/

module

public import LeanVM.Guest.B1.Eq.RsRows

/-!
# `rs_eq_rows_all` (lean_ethereum.py)

`rs_eq_rows_all(row, zs, ps, n)` is `rs_eq_rows` keeping every row: it reads the `n` coordinates
`zs[i]`, `ps[i]`, and for each `k < 64` the row word `row[k]`, multiplies it by
`zs[i]^(2^k) + ps[i]` for `i < n` and stores each partial product, after coordinate `i`, at
`row·g^(64 (i + 1) + k)`; it returns `0`. Its values are `rs_eq_rows__L{n}`'s (`rrS`, `rrZ`,
`rrAcc`, `RsRows.lean`), each coordinate adding a store (`rraCoord`); `rraBody n` is equal to each
specialization by kernel evaluation. `rs_eq_rows_all_holds`: the core IR gives
`MeaningRsEqRowsAll`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The meaning -/

/-- **`rs_eq_rows_all(row, zs, ps, n)`**: it returns `0`; at `n > 0`, the `n` words `zs`, `ps` at
`zs`, `ps` and the 64 words `c` at `row`, row `i + 1` (64 words from `row·g^(64 (i + 1))`), `i < n`,
holds `ringRow c[k] zs[..i+1] ps[..i+1] k` at `k < 64`. -/
def MeaningRsEqRowsAll (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [row, z, p], rets => rets = [0] ∧ (0 < n →
      ∃ zs ps c : List E, zs.length = n ∧ ps.length = n ∧ c.length = 64 ∧
        ReadsAt rd z zs ∧ ReadsAt rd p ps ∧ ReadsAt rd row c ∧
        ∀ i < n, ∀ k < 64, LoadHolds rd row (64 * (i + 1) + k)
          (ringRow (c.getD k 0) (zs.take (i + 1)) (ps.take (i + 1)) k))
  | _, _ => False

/-- The specializations' names, `rs_eq_rows_all__L{n}`, `n ≤ 8` (`RS_CHUNK = 8`). -/
def rsEqRowsAllNames : List String :=
  ["rs_eq_rows_all__L0", "rs_eq_rows_all__L1", "rs_eq_rows_all__L2", "rs_eq_rows_all__L3",
    "rs_eq_rows_all__L4", "rs_eq_rows_all__L5", "rs_eq_rows_all__L6", "rs_eq_rows_all__L7",
    "rs_eq_rows_all__L8"]

/-- `rs_eq_rows_all__L{n}`'s core IR gives its meaning, `n ≤ 8`. -/
def rs_eq_rows_all_Spec : Prop :=
  ∀ n ≤ 8, ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd (rsEqRowsAllNames.getD n "") args rets → MeaningRsEqRowsAll n rd args rets

/-! ## The template -/

/-- Coordinate `i` of row `k`, its partial product stored at `row·g^(64 (i + 1) + k)`. -/
def rraCoord (n k i : ℕ) : List Stmt :=
  rrCoord n k i ++ [.atom (.load (.n (rrS n k + 2 + rrStride k * i)) (.n 0) (64 * (i + 1) + k))]

/-- Row `k`: its word, then the coordinates. -/
def rraRow (n k : ℕ) : List Stmt :=
  [.atom (.load (.n (rrS n k)) (.n 0) k)] ++ ((List.range n).map (rraCoord n k)).flatten

/-- The coordinates' reads. -/
def rraHeadBlk (i : ℕ) : List Stmt :=
  [.atom (.load (.n (3 + 2 * i)) (.n 1) i), .atom (.load (.n (4 + 2 * i)) (.n 2) i)]

/-- **The expansion of `rs_eq_rows_all__L{n}`.** -/
def rraBody (n : ℕ) : List Stmt :=
  ((List.range n).map rraHeadBlk).flatten ++ ((List.range 64).map (rraRow n)).flatten ++
    [.atom (.const (.n (rrT n)) (word 0 0)), .ret [.n (rrT n)]]

theorem rs_eq_rows_all_L1_body : Fn.body fn% «rs_eq_rows_all__L1» = rraBody 1 :=
  stmtsEqb_sound (by decide +kernel)
theorem rs_eq_rows_all_L2_body : Fn.body fn% «rs_eq_rows_all__L2» = rraBody 2 :=
  stmtsEqb_sound (by decide +kernel)
theorem rs_eq_rows_all_L3_body : Fn.body fn% «rs_eq_rows_all__L3» = rraBody 3 :=
  stmtsEqb_sound (by decide +kernel)
theorem rs_eq_rows_all_L4_body : Fn.body fn% «rs_eq_rows_all__L4» = rraBody 4 :=
  stmtsEqb_sound (by decide +kernel)
theorem rs_eq_rows_all_L5_body : Fn.body fn% «rs_eq_rows_all__L5» = rraBody 5 :=
  stmtsEqb_sound (by decide +kernel)
theorem rs_eq_rows_all_L6_body : Fn.body fn% «rs_eq_rows_all__L6» = rraBody 6 :=
  stmtsEqb_sound (by decide +kernel)
theorem rs_eq_rows_all_L7_body : Fn.body fn% «rs_eq_rows_all__L7» = rraBody 7 :=
  stmtsEqb_sound (by decide +kernel)
theorem rs_eq_rows_all_L8_body : Fn.body fn% «rs_eq_rows_all__L8» = rraBody 8 :=
  stmtsEqb_sound (by decide +kernel)

/-! ## The conditions -/

/-- Row `k`'s conditions. -/
def RraRowOk (rd : Reader) (σ : Val) (n k : ℕ) : Prop :=
  LoadHolds rd (σ (.n 0)) k (σ (.n (rrS n k))) ∧
    ∀ i < n, RrCoordOk σ n k i ∧
      LoadHolds rd (σ (.n 0)) (64 * (i + 1) + k) (σ (.n (rrS n k + 2 + rrStride k * i)))

theorem rraCoord_noRet (n k i : ℕ) : Stmt.noRetList (rraCoord n k i) = true := by
  rw [rraCoord, noRetList_append', rrCoord_noRet]; rfl

theorem holds_rraCoord {C : CallRel} {rd : Reader} {σ : Val} (n k i : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (rraCoord n k i) True kret ↔
      RrCoordOk σ n k i ∧
        LoadHolds rd (σ (.n 0)) (64 * (i + 1) + k) (σ (.n (rrS n k + 2 + rrStride k * i))) := by
  rw [rraCoord, holdsList_append]
  unfold rrCoord RrCoordOk
  split <;> simp_all [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_assoc]

theorem rraRow_noRet (n k : ℕ) : Stmt.noRetList (rraRow n k) = true := by
  rw [rraRow, noRetList_append', noRetList_flatten_range _ _ (rraCoord_noRet n k)]
  rfl

theorem holds_rraRow {C : CallRel} {rd : Reader} {σ : Val} (n k : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (rraRow n k) True kret ↔ RraRowOk rd σ n k := by
  rw [rraRow, holdsList_append, holdsList_range_flatten n (rraCoord n k) (rraCoord_noRet n k)]
  simp only [holds_rraCoord, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, RraRowOk]

theorem rraZ_pow {rd : Reader} {σ : Val} {n : ℕ} (h : ∀ k < 64, RraRowOk rd σ n k) :
    ∀ k < 64, ∀ i < n, σ (.n (rrZ n k i)) = σ (.n (3 + 2 * i)) ^ 2 ^ k
  | 0, _, i, _ => by simp [rrZ]
  | k + 1, hk, i, hi => by
    rw [rrZ, (((h k (by omega)).2 i hi).1).2.2 (by omega), rraZ_pow h k (by omega) i hi, ← pow_add,
      ← two_mul, ← pow_succ']

theorem rraAcc_eq {rd : Reader} {σ : Val} {n : ℕ} (h : ∀ k < 64, RraRowOk rd σ n k) (k : ℕ)
    (hk : k < 64) :
    ∀ i ≤ n, σ (.n (rrAcc n k i)) = ringRow (σ (.n (rrS n k)))
      (((List.range n).map fun i ↦ σ (.n (3 + 2 * i))).take i)
      (((List.range n).map fun i ↦ σ (.n (4 + 2 * i))).take i) k
  | 0, _ => by rw [ringRow_nil]; rfl
  | i + 1, hi => by
    obtain ⟨e1, e2, -⟩ := ((h k hk).2 i (by omega)).1
    rw [ringRow_take_succ _ _ _ _ _ (by simp; omega) (by simp; omega), ← rraAcc_eq h k hk i (by omega)]
    simp only [List.getElem_map, List.getElem_range]
    rw [show rrAcc n k (i + 1) = rrS n k + 2 + rrStride k * i from rfl, e2, e1,
      rraZ_pow h k hk i (by omega)]

/-! ## Soundness -/

theorem rra_sound {name : String} {f : Fn} (n : ℕ) (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2]) (hbody : f.body = rraBody n) (rd : Reader)
    (args rets : List E) (h : coreProgram.Rel rd name args rets) : MeaningRsEqRowsAll n rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams, rraBody] at h
  simp only [holdsList_append, holdsList_range_flatten n rraHeadBlk (fun _ ↦ rfl),
    holdsList_range_flatten 64 (rraRow n) (rraRow_noRet n), holds_rraRow,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at h
  obtain ⟨σ, hp, hh, hr, hT, hret⟩ := h
  subst hp hret
  have hh' : ∀ i < n, LoadHolds rd (σ (.n 1)) i (σ (.n (3 + 2 * i))) ∧
      LoadHolds rd (σ (.n 2)) i (σ (.n (4 + 2 * i))) := fun i hi ↦ by
    have := hh i hi
    simpa [rraHeadBlk, Stmt.HoldsList, Stmt.Holds, Atom.Holds] using this
  refine ⟨by rw [hT, word_zero], fun _ ↦ ⟨(List.range n).map (fun i ↦ σ (.n (3 + 2 * i))),
    (List.range n).map (fun i ↦ σ (.n (4 + 2 * i))), (List.range 64).map (fun k ↦ σ (.n (rrS n k))),
    by simp, by simp, by simp, readsAt_range fun i hi ↦ (hh' i hi).1,
    readsAt_range fun i hi ↦ (hh' i hi).2, readsAt_range fun k hk ↦ (hr k hk).1,
    fun i hi k hk ↦ ?_⟩⟩
  have := ((hr k hk).2 i hi).2
  rw [show rrS n k + 2 + rrStride k * i = rrAcc n k (i + 1) from rfl,
    rraAcc_eq hr k hk (i + 1) (by omega)] at this
  convert this using 2
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

theorem rra0_sound (rd : Reader) (args rets : List E)
    (h : coreProgram.Rel rd "rs_eq_rows_all__L0" args rets) : MeaningRsEqRowsAll 0 rd args rets := by
  have hb : Fn.body fn% «rs_eq_rows_all__L0» = [.atom (.const (.n 3) (word 0 0)), .ret [.n 3]] :=
    stmtsEqb_sound (by decide +kernel)
  rw [rel_iff_sem (coreProgram_find?_at (j := idx% «rs_eq_rows_all__L0») rfl), hb] at h
  obtain ⟨σ, hp, h⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at h
  obtain ⟨h3, hret⟩ := h
  have hpar : Fn.params fn% «rs_eq_rows_all__L0» = [.n 0, .n 1, .n 2] := rfl
  rw [hpar] at hp
  simp only [List.map_cons, List.map_nil] at hp
  subst hp hret
  exact ⟨by rw [h3, word_zero], fun h0 ↦ absurd h0 (lt_irrefl 0)⟩

set_option maxRecDepth 100000 in
/-- **`rs_eq_rows_all`'s core IR gives its meaning**, `n ≤ 8`. -/
theorem rs_eq_rows_all_holds : rs_eq_rows_all_Spec := by
  intro n hn rd args rets h
  interval_cases n
  · exact rra0_sound rd args rets h
  · exact rra_sound 1 (coreProgram_find?_at (j := idx% «rs_eq_rows_all__L1») rfl) rfl
      rs_eq_rows_all_L1_body rd args rets h
  · exact rra_sound 2 (coreProgram_find?_at (j := idx% «rs_eq_rows_all__L2») rfl) rfl
      rs_eq_rows_all_L2_body rd args rets h
  · exact rra_sound 3 (coreProgram_find?_at (j := idx% «rs_eq_rows_all__L3») rfl) rfl
      rs_eq_rows_all_L3_body rd args rets h
  · exact rra_sound 4 (coreProgram_find?_at (j := idx% «rs_eq_rows_all__L4») rfl) rfl
      rs_eq_rows_all_L4_body rd args rets h
  · exact rra_sound 5 (coreProgram_find?_at (j := idx% «rs_eq_rows_all__L5») rfl) rfl
      rs_eq_rows_all_L5_body rd args rets h
  · exact rra_sound 6 (coreProgram_find?_at (j := idx% «rs_eq_rows_all__L6») rfl) rfl
      rs_eq_rows_all_L6_body rd args rets h
  · exact rra_sound 7 (coreProgram_find?_at (j := idx% «rs_eq_rows_all__L7») rfl) rfl
      rs_eq_rows_all_L7_body rd args rets h
  · exact rra_sound 8 (coreProgram_find?_at (j := idx% «rs_eq_rows_all__L8») rfl) rfl
      rs_eq_rows_all_L8_body rd args rets h

end
end LeanVM.Guest.B1
