/-
  LeanVM.Guest.B1.Ring.Cols

  B1 of `ring_cols`: a table's ring pieces' weight at their shared row, every specialization.
-/

module

public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.B1.Ring.Lib
public import LeanVM.Guest.B1.Common.Find
public import LeanVM.Guest.Data.NameStrings

/-!
# `ring_cols`

`ring_cols(row, scl, msk, n)` (`guests/lean_ethereum.py`) reads the 64 words `r_k` of a row, and
for each of `n` columns its scale `s_q` and its selector `m_q`; it returns
`Σ_q m_q Σ_k r_k s_q^(2^k)` (`MeaningRingCols`): the ring weight of a table's pointer columns at
their shared row (`ringWeight`, `ring_switch.rs`), the row holding the map's coefficients times
the products of the row point's `eq` factors (`ring_rows`). Its expansion, `rcBody n`: the row's
loads (`rcLoads`), then per column its scale, the Frobenius chain of `63` squarings, each scaled
by the row's word and summed (`rcStep`), its selector and the running total (`rcColQ`), then a
copy and the return. `ring_cols_holds`: every specialization (`n = 3, 5, 10`) computes its
meaning.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The meaning -/

/-- The Frobenius sum of a row at a scale: `Σ_{k < 64} r_k s^(2^k)`. -/
def frobSum (rs : List E) (s : E) : E := ∑ k ∈ Finset.range kBits, rs.getD k 0 * s ^ 2 ^ k

/-- **`ring_cols(row, scl, msk)`** at `n` columns: the 64 words `rs` at `row`, the `n` scales `ss`
at `scl` and the `n` selectors `ms` at `msk`; it returns `Σ_q m_q · frobSum rs s_q`. -/
def MeaningRingCols (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [row, scl, msk], rets =>
      ∃ rs ss ms : List E, rs.length = kBits ∧ ss.length = n ∧ ms.length = n ∧
        ReadsAt rd row rs ∧ ReadsAt rd scl ss ∧ ReadsAt rd msk ms ∧
        rets = [∑ q ∈ Finset.range n, ms.getD q 0 * frobSum rs (ss.getD q 0)]
  | _, _ => False

/-- The deployed specializations: column count and name. -/
def ringColsNames : List (ℕ × String) := [(3, "ring_cols__L3"), (5, "ring_cols__L5"), (10, "ring_cols__L10")]

/-- `ring_cols`' core IR computes its meaning, at every deployed specialization. -/
def ring_cols_Spec : Prop :=
  ∀ p ∈ ringColsNames, ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd p.2 args rets → MeaningRingCols p.1 rd args rets

/-! ## The template -/

/-- The row's 64 words, at the values `3 ..< 67`. -/
def rcLoad (k : ℕ) : List Stmt := [.atom (.load (.n (3 + k)) (.n 0) k)]

/-- The scale's power `s^(2^j)` of the column at `b`. -/
def rcSq (b j : ℕ) : ℕ := if j = 0 then b else b + 3 * j - 1

/-- The column at `b`'s running sum after its word `j`. -/
def rcAc (b j : ℕ) : ℕ := if j = 0 then b + 1 else b + 3 * j + 1

/-- Step `j + 1` of the column at `b`: square, scale by the row's word, add. -/
def rcStep (b j : ℕ) : List Stmt :=
  [.atom (.mul (.n (b + 3 * j + 2)) (.n (rcSq b j)) (.n (rcSq b j))),
    .atom (.mul (.n (b + 3 * j + 3)) (.n (4 + j)) (.n (b + 3 * j + 2))),
    .atom (.add (.n (b + 3 * j + 4)) (.n (rcAc b j)) (.n (b + 3 * j + 3)))]

/-- Column `q` at `b`: its scale, the chain, its selector and their product. -/
def rcCol (b q : ℕ) : List Stmt :=
  [.atom (.load (.n b) (.n 1) q), .atom (.mul (.n (b + 1)) (.n 3) (.n b))] ++
    ((List.range 63).map (rcStep b)).flatten ++
    [.atom (.load (.n (b + 191)) (.n 2) q), .atom (.mul (.n (b + 192)) (.n (b + 190)) (.n (b + 191)))]

/-- Column `q`'s first value. -/
def rcBase (q : ℕ) : ℕ := if q = 0 then 67 else 66 + 194 * q

/-- The running total after column `q`. -/
def rcTot (q : ℕ) : ℕ := 259 + 194 * q

/-- Column `q`, added to the total. -/
def rcColQ (q : ℕ) : List Stmt :=
  rcCol (rcBase q) q ++
    if q = 0 then [] else [.atom (.add (.n (rcTot q)) (.n (rcTot (q - 1))) (.n (rcBase q + 192)))]

/-- **The expansion of `ring_cols__L{n}`.** -/
def rcBody (n : ℕ) : List Stmt :=
  ((List.range 64).map rcLoad).flatten ++ ((List.range n).map rcColQ).flatten ++
    [.atom (.copy (.n (rcTot (n - 1) + 1)) (.n (rcTot (n - 1)))), .ret [.n (rcTot (n - 1) + 1)]]

theorem ring_cols_L3_body : Fn.body fn% «ring_cols__L3» = rcBody 3 := stmtsEqb_sound (by decide +kernel)

theorem ring_cols_L5_body : Fn.body fn% «ring_cols__L5» = rcBody 5 := stmtsEqb_sound (by decide +kernel)

theorem ring_cols_L10_body : Fn.body fn% «ring_cols__L10» = rcBody 10 := stmtsEqb_sound (by decide +kernel)

/-! ## Soundness -/

theorem rcStep_noRet (b j : ℕ) : Stmt.noRetList (rcStep b j) = true := rfl

theorem rcCol_noRet (b q : ℕ) : Stmt.noRetList (rcCol b q) = true := by
  rw [rcCol, ringNoRetList_append, ringNoRetList_append, ringNoRetList_flatten_map _ (rcStep_noRet b) _]; rfl

theorem rcColQ_noRet (q : ℕ) : Stmt.noRetList (rcColQ q) = true := by
  rw [rcColQ, ringNoRetList_append, rcCol_noRet]; split <;> rfl

/-- What column `q` at `b` gives, from the row's words `r`: its scale `s` and selector `m` are read,
and its product is `m · Σ_{k < 64} r_k s^(2^k)`. -/
theorem rcCol_val {b q : ℕ} {next : Prop} {kret : List E → Prop} (r : ℕ → E)
    (hr : ∀ k < 64, σ (.n (3 + k)) = r k) (h : Stmt.HoldsList C rd σ (rcCol b q) next kret) :
    LoadHolds rd (σ (.n 1)) q (σ (.n b)) ∧ LoadHolds rd (σ (.n 2)) q (σ (.n (b + 191))) ∧
      σ (.n (b + 192)) = σ (.n (b + 191)) *
        ∑ k ∈ Finset.range 64, r k * σ (.n b) ^ 2 ^ k ∧ next := by
  rw [rcCol, holdsList_append, holdsList_append] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨ls, e1, h⟩ := h
  obtain ⟨hst, lm, e192, hn⟩ := (holdsList_range_flatten 63 (rcStep b) (rcStep_noRet b) _ _).mp h
  -- the chain, word by word
  have hch : ∀ j ≤ 63, σ (.n (rcSq b j)) = σ (.n b) ^ 2 ^ j ∧
      σ (.n (rcAc b j)) = ∑ k ∈ Finset.range (j + 1), r k * σ (.n b) ^ 2 ^ k := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨by simp [rcSq], ?_⟩
      simp only [rcAc, ↓reduceIte, zero_add, Finset.sum_range_one, pow_zero, pow_one]
      rw [e1, hr 0 (by decide)]
    | succ j ih =>
      intro hj
      obtain ⟨ihs, iha⟩ := ih (by omega)
      have hs := hst j (by omega)
      simp only [rcStep, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
      obtain ⟨m1, m2, a3, -⟩ := hs
      have esq : rcSq b (j + 1) = b + 3 * j + 2 := by
        simp only [rcSq, Nat.add_one_ne_zero, ↓reduceIte]; omega
      have eac : rcAc b (j + 1) = b + 3 * j + 4 := by
        simp only [rcAc, Nat.add_one_ne_zero, ↓reduceIte]; omega
      rw [esq, eac]
      have hsq : σ (.n (b + 3 * j + 2)) = σ (.n b) ^ 2 ^ (j + 1) := by
        rw [m1, ihs, ← pow_two, ← pow_mul, pow_succ]
      refine ⟨hsq, ?_⟩
      rw [a3, iha, m2, hsq, show 4 + j = 3 + (j + 1) by omega, hr (j + 1) (by omega),
        Finset.sum_range_succ _ (j + 1)]
  have h63 := (hch 63 le_rfl).2
  have e63 : rcAc b 63 = b + 190 := by simp [rcAc]
  rw [e63] at h63
  exact ⟨ls, lm, by rw [e192, h63, mul_comm], hn⟩

/-- **`ring_cols__L{n}` computes its meaning**, from its template. -/
theorem ring_cols_sound {name : String} {f : Fn} (n : ℕ) (hn : 1 ≤ n)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1, .n 2])
    (hbody : f.body = rcBody n) (rd : Reader) (args rets : List E)
    (h : coreProgram.Rel rd name args rets) : MeaningRingCols n rd args rets := by
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem hfind args rets).mp h
  rw [hparams] at hpar
  simp only [List.map_cons, List.map_nil] at hpar
  subst hpar
  rw [hbody, rcBody, holdsList_append, holdsList_append] at hb
  obtain ⟨hl, hb⟩ := (holdsList_range_flatten 64 rcLoad (fun _ ↦ rfl) _ _).mp hb
  obtain ⟨hc, hb⟩ := (holdsList_range_flatten n rcColQ rcColQ_noRet _ _).mp hb
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hb
  obtain ⟨ecp, hret⟩ := hb
  -- the row
  have hlk : ∀ k < 64, LoadHolds rd (σ (.n 0)) k (σ (.n (3 + k))) := fun k hk ↦ by
    have := hl k hk
    simp only [rcLoad, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at this
    exact this.1
  set rs : List E := (List.range 64).map fun k ↦ σ (.n (3 + k)) with hrs
  have hrs_get : ∀ k < 64, rs.getD k 0 = σ (.n (3 + k)) := fun k hk ↦ by
    simp [hrs, List.getD_eq_getElem?_getD, hk]
  -- the columns
  have hcol : ∀ q < n, LoadHolds rd (σ (.n 1)) q (σ (.n (rcBase q))) ∧
      LoadHolds rd (σ (.n 2)) q (σ (.n (rcBase q + 191))) ∧
      σ (.n (rcBase q + 192)) = σ (.n (rcBase q + 191)) * frobSum rs (σ (.n (rcBase q))) ∧
      (q ≠ 0 → σ (.n (rcTot q)) = σ (.n (rcTot (q - 1))) + σ (.n (rcBase q + 192))) := by
    intro q hq
    have hq' := hc q hq
    rw [rcColQ, holdsList_append] at hq'
    obtain ⟨l1, l2, ev, hnext⟩ := rcCol_val (fun k ↦ rs.getD k 0)
      (fun k hk ↦ (hrs_get k hk).symm) hq'
    refine ⟨l1, l2, by rw [ev]; rfl, fun hq0 ↦ ?_⟩
    simp only [hq0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hnext
    exact hnext.1
  have hbase0 : rcBase 0 + 192 = rcTot 0 := rfl
  have htot : ∀ q < n, σ (.n (rcTot q)) = ∑ q' ∈ Finset.range (q + 1),
      σ (.n (rcBase q' + 191)) * frobSum rs (σ (.n (rcBase q'))) := by
    intro q
    induction q with
    | zero =>
      intro hq
      rw [Finset.sum_range_one, ← hbase0, (hcol 0 hq).2.2.1]
    | succ q ih =>
      intro hq
      rw [(hcol (q + 1) hq).2.2.2 (by omega), Nat.add_sub_cancel, ih (by omega),
        (hcol (q + 1) hq).2.2.1, Finset.sum_range_succ _ (q + 1)]
  refine ⟨rs, (List.range n).map fun q ↦ σ (.n (rcBase q)),
    (List.range n).map fun q ↦ σ (.n (rcBase q + 191)), by simp [hrs, kBits], by simp, by simp,
    fun k hk ↦ ?_, fun q hq ↦ ?_, fun q hq ↦ ?_, ?_⟩
  · simp only [hrs, List.length_map, List.length_range] at hk
    simpa [hrs] using hlk k hk
  · simp only [List.length_map, List.length_range] at hq
    simpa using (hcol q hq).1
  · simp only [List.length_map, List.length_range] at hq
    simpa using (hcol q hq).2.1
  · rw [← hret, ecp, htot (n - 1) (by omega), Nat.sub_add_cancel hn, List.cons.injEq]
    refine ⟨Finset.sum_congr rfl fun q hq ↦ ?_, rfl⟩
    have hq' := Finset.mem_range.mp hq
    simp [List.getD_eq_getElem?_getD, hq']

set_option maxRecDepth 100000 in
theorem ring_cols_L3_holds (rd : Reader) (args rets : List E)
    (h : coreProgram.Rel rd "ring_cols__L3" args rets) : MeaningRingCols 3 rd args rets :=
  ring_cols_sound 3 (by decide) (coreProgram_find?_at (j := idx% «ring_cols__L3») rfl) rfl
    ring_cols_L3_body rd args rets h

set_option maxRecDepth 100000 in
theorem ring_cols_L5_holds (rd : Reader) (args rets : List E)
    (h : coreProgram.Rel rd "ring_cols__L5" args rets) : MeaningRingCols 5 rd args rets :=
  ring_cols_sound 5 (by decide) (coreProgram_find?_at (j := idx% «ring_cols__L5») rfl) rfl
    ring_cols_L5_body rd args rets h

set_option maxRecDepth 100000 in
theorem ring_cols_L10_holds (rd : Reader) (args rets : List E)
    (h : coreProgram.Rel rd "ring_cols__L10" args rets) : MeaningRingCols 10 rd args rets :=
  ring_cols_sound 10 (by decide) (coreProgram_find?_at (j := idx% «ring_cols__L10») rfl) rfl
    ring_cols_L10_body rd args rets h

/-- **`ring_cols` computes its meaning**, every deployed specialization. -/
theorem ring_cols_holds : ring_cols_Spec := by
  intro p hp
  simp only [ringColsNames, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl
  exacts [ring_cols_L3_holds, ring_cols_L5_holds, ring_cols_L10_holds]

end
end LeanVM.Guest.B1.VerifySub
