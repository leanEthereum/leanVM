/-
  LeanVM.Guest.B1.Whir.CFinB

  The finish's basis rows, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CFinEval
public import LeanVM.Guest.B1.Whir.Bases
public import LeanVM.Guest.B1.Whir.CCalls

/-!
# The basis rows, honestly

`osAfterRow_complete`: the product of a level's coordinates.
`osBasisBlk_complete`: one coordinate: its challenge loaded, its coefficient (times the vanishing
inverse), `d = (1 + c)/(coefficient·(1 + z) + z)` stored in `basis_d` at the level's zero flag `z`,
the scale advanced. `osBasisLv_complete`: a non-final level's row, its `β` loaded from
`level_scales`, its product, its flag (`is_zero`), its coordinates, its scale and product stored
in `level_scale` and `level_after`; `osBases_complete`: every non-final level's, their calls'
values `basesCV`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {M : Reader → Prop} {H : CallRel → Reader → Prop}

/-! ## The product of the coordinates -/

/-- **The product of the coordinates, honestly**: each loaded, the running product advanced. -/
theorem osAfterRow_complete (X : ℕ → E) : ∀ (srcs : List (ℕ × ℕ)) (prev : Option ℕ) (k : ℕ) (σ : Val),
    (∀ x, prev = some x → x < k) →
    (∀ t < srcs.length, (srcs.getD t (0, 0)).1 < k ∧ ∀ C rd, HM M H C rd →
      LoadHolds rd (σ (.n (srcs.getD t (0, 0)).1)) (srcs.getD t (0, 0)).2 (X t)) →
    BlkA M H σ k (osAfterRow srcs prev k).2.2 (osAfterRow srcs prev k).1
      (fun σ' ↦ (prev.isSome ∨ srcs ≠ []) → σ' (.n ((osAfterRow srcs prev k).2.1.getD 0)) =
        optVal σ' prev * ∏ t ∈ Finset.range srcs.length, X t)
  | [], prev, k, σ, _, _ => by
    refine BlkA.nil fun σ' _ h ↦ ?_
    rcases prev with _ | x
    · simp at h
    · simp [osAfterRow, optVal]
  | src :: rest, none, k, σ, _, hin => by
    obtain ⟨hs0, hl0⟩ := hin 0 (by simp)
    simp only [List.getD_cons_zero] at hs0 hl0
    have hA : BlkA M H σ k (k + 1) [osLd k src.1 src.2] (fun σ' ↦ σ' (.n k) = X 0) :=
      blk_lst [X 0] (by simp) fun C rd hH σ' ha hv ↦ by
        have v0 := hv 0 (by simp)
        simp only [List.getD_cons_zero, Nat.add_zero] at v0
        simp only [osLd, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load]
        rw [v0, ha _ hs0]
        exact ⟨hl0 C rd hH, rfl⟩
    have hB := BlkA.seq (M := M) (H := H) (by omega) (osAfterRow_next rest (some k) (k + 1)).1 hA.agree
      fun σ1 ha1 _ ↦ osAfterRow_complete (fun t ↦ X (t + 1)) rest (some k) (k + 1) σ1
        (fun x hx ↦ by simp only [Option.some.injEq] at hx; omega) fun t ht ↦ by
          obtain ⟨a, b⟩ := hin (t + 1) (by simp; omega)
          simp only [List.getD_cons_succ] at a b
          exact ⟨by omega, fun C rd hH ↦ by rw [ha1 _ a]; exact b C rd hH⟩
    simp only [osAfterRow]
    refine hB.mono fun σ' ⟨⟨o1, _⟩, o2⟩ _ ↦ ?_
    rw [o2 (Or.inl rfl), List.length_cons, Finset.prod_range_succ', optVal, optVal, o1]
    ring
  | src :: rest, some p, k, σ, hp, hin => by
    have hpk := hp p rfl
    obtain ⟨hs0, hl0⟩ := hin 0 (by simp)
    simp only [List.getD_cons_zero] at hs0 hl0
    have hA : BlkA M H σ k (k + 2) [osLd k src.1 src.2, osMul (k + 1) p k]
        (fun σ' ↦ σ' (.n (k + 1)) = σ' (.n p) * X 0) :=
      blk_lst [X 0, σ (.n p) * X 0] (by simp) fun C rd hH σ' ha hv ↦ by
        have v0 := hv 0 (by simp)
        have v1 := hv 1 (by simp)
        simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1
        simp only [osLd, osMul, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, holds_mul]
        rw [v0, v1, ha _ hs0, ha _ hpk]
        exact ⟨⟨hl0 C rd hH, rfl⟩, rfl⟩
    have hB := BlkA.seq (M := M) (H := H) (by omega) (osAfterRow_next rest (some (k + 1)) (k + 2)).1 hA.agree
      fun σ1 ha1 _ ↦ osAfterRow_complete (fun t ↦ X (t + 1)) rest (some (k + 1)) (k + 2) σ1
        (fun x hx ↦ by simp only [Option.some.injEq] at hx; omega) fun t ht ↦ by
          obtain ⟨a, b⟩ := hin (t + 1) (by simp; omega)
          simp only [List.getD_cons_succ] at a b
          exact ⟨by omega, fun C rd hH ↦ by rw [ha1 _ a]; exact b C rd hH⟩
    simp only [osAfterRow]
    refine hB.mono fun σ' ⟨⟨o1, _⟩, o2⟩ _ ↦ ?_
    rw [o2 (Or.inl rfl), List.length_cons, Finset.prod_range_succ', optVal, optVal, o1]
    ring

theorem osAfterRow_isSome : ∀ (srcs : List (ℕ × ℕ)) (prev : Option ℕ) (k : ℕ),
    (prev.isSome ∨ srcs ≠ []) → (osAfterRow srcs prev k).2.1.isSome
  | [], prev, k, h => by simpa [osAfterRow] using h
  | _ :: rest, none, k, _ => by
    simp only [osAfterRow]; exact osAfterRow_isSome rest _ _ (Or.inl rfl)
  | _ :: rest, some _, k, _ => by
    simp only [osAfterRow]; exact osAfterRow_isSome rest _ _ (Or.inl rfl)

/-! ## One coordinate -/

theorem osBasisBlk_next (bd slot : ℕ) (src : ℕ × ℕ) (inv sc z nz : ℕ) (k : ℕ) :
    k + 6 ≤ (osBasisBlk bd slot src inv sc z nz k).2.2 ∧
      (osBasisBlk bd slot src inv sc z nz k).2.1 < (osBasisBlk bd slot src inv sc z nz k).2.2 := by
  unfold osBasisBlk
  dsimp only
  split_ifs <;> simp

/-- **One coordinate of a basis row, honestly**, at the level's zero flag `zv`. -/
theorem osBasisBlk_complete {σ : Val} {bd slot : ℕ} {src : ℕ × ℕ} {inv sc z nz : ℕ} {k : ℕ}
    {cv zv : E} (hsrc : src.1 < k) (hbd : bd < k) (hsc : sc < k) (hz : z < k) (hnz : nz < k)
    (hzv : σ (.n z) = zv) (hnzv : σ (.n nz) = 1 + zv)
    (hden : cv * word inv 0 * (1 + zv) + zv ≠ 0)
    (hcv : ∀ C rd, HM M H C rd → LoadHolds rd (σ (.n src.1)) src.2 cv)
    (hst : ∀ C rd, HM M H C rd → LoadHolds rd (σ (.n bd)) slot (dZv cv (word inv 0) zv)) :
    BlkA M H σ k (osBasisBlk bd slot src inv sc z nz k).2.2 (osBasisBlk bd slot src inv sc z nz k).1
      (fun σ' ↦ σ' (.n (osBasisBlk bd slot src inv sc z nz k).2.1) = σ (.n sc) * (cv * word inv 0)) := by
  obtain ⟨s1, s2⟩ := src
  simp only at hsrc hcv
  by_cases hi : inv = 1
  · subst hi
    have hden' : cv * (1 + zv) + zv ≠ 0 := by rwa [word_one, mul_one] at hden
    have e : osBasisBlk bd slot (s1, s2) 1 sc z nz k =
        ([osLd k s1 s2, osCst (k + 1) (word 1 0), osAdd (k + 2) (k + 1) k, osCst (k + 3) (word 1 0),
          osMul (k + 4) k nz, osAdd (k + 5) (k + 4) z, osMul (k + 3) (k + 6) (k + 5),
          osMul (k + 7) (k + 2) (k + 6), osLd (k + 7) bd slot, osMul (k + 8) sc k], k + 8, k + 9) := by
      simp [osBasisBlk]
    rw [e]
    refine blk_lst [cv, word 1 0, word 1 0 + cv, word 1 0, cv * (1 + zv), cv * (1 + zv) + zv,
      1 / (cv * (1 + zv) + zv), dZv cv (word 1 0) zv, σ (.n sc) * cv] (by simp)
      fun C rd hH σ' ha hv ↦ ?_
    have v0 := hv 0 (by simp)
    have v1 := hv 1 (by simp)
    have v2 := hv 2 (by simp)
    have v3 := hv 3 (by simp)
    have v4 := hv 4 (by simp)
    have v5 := hv 5 (by simp)
    have v6 := hv 6 (by simp)
    have v7 := hv 7 (by simp)
    have v8 := hv 8 (by simp)
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4 v5 v6 v7 v8
    simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, holds_const, holds_add,
      holds_mul, osLd, osCst, osAdd, osMul]
    rw [v0, v1, v2, v3, v4, v5, v6, v7, v8, ha _ hsrc, ha _ hbd, ha _ hsc, ha _ hz, ha _ hnz, hzv, hnzv]
    refine ⟨⟨hcv C rd hH, rfl, rfl, rfl, rfl, rfl, ?_, ?_, hst C rd hH, rfl⟩, by rw [word_one, mul_one]⟩
    · rw [word_one, one_div_mul_cancel hden']
    · rw [dZv, word_one, mul_one, mul_one_div]
  · have e : osBasisBlk bd slot (s1, s2) inv sc z nz k =
        ([osLd k s1 s2, osCst (k + 1) (word inv 0), osMul (k + 2) k (k + 1), osCst (k + 3) (word 1 0),
          osAdd (k + 4) (k + 3) k, osCst (k + 5) (word 1 0), osMul (k + 6) (k + 2) nz,
          osAdd (k + 7) (k + 6) z, osMul (k + 5) (k + 8) (k + 7), osMul (k + 9) (k + 4) (k + 8),
          osLd (k + 9) bd slot, osMul (k + 10) sc (k + 2)], k + 10, k + 11) := by
      simp [osBasisBlk, hi]
    rw [e]
    refine blk_lst [cv, word inv 0, cv * word inv 0, word 1 0, word 1 0 + cv, word 1 0,
      cv * word inv 0 * (1 + zv), cv * word inv 0 * (1 + zv) + zv,
      1 / (cv * word inv 0 * (1 + zv) + zv), dZv cv (word inv 0) zv,
      σ (.n sc) * (cv * word inv 0)] (by simp) fun C rd hH σ' ha hv ↦ ?_
    have v0 := hv 0 (by simp)
    have v1 := hv 1 (by simp)
    have v2 := hv 2 (by simp)
    have v3 := hv 3 (by simp)
    have v4 := hv 4 (by simp)
    have v5 := hv 5 (by simp)
    have v6 := hv 6 (by simp)
    have v7 := hv 7 (by simp)
    have v8 := hv 8 (by simp)
    have v9 := hv 9 (by simp)
    have v10 := hv 10 (by simp)
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
    simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, holds_const, holds_add,
      holds_mul, osLd, osCst, osAdd, osMul]
    rw [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, ha _ hsrc, ha _ hbd, ha _ hsc, ha _ hz, ha _ hnz,
      hzv, hnzv]
    refine ⟨⟨hcv C rd hH, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, hst C rd hH, rfl⟩, rfl⟩
    · rw [word_one, one_div_mul_cancel hden]
    · rw [dZv, word_one, mul_one_div]

theorem osBasisRow_next (bd : ℕ) : ∀ (cs : List (ℕ × (ℕ × ℕ) × ℕ)) (sc z nz k : ℕ),
    k ≤ (osBasisRow bd cs sc z nz k).2.2 ∧
      (cs ≠ [] → (osBasisRow bd cs sc z nz k).2.1 < (osBasisRow bd cs sc z nz k).2.2)
  | [], _, _, _, _ => ⟨le_rfl, fun h ↦ absurd rfl h⟩
  | (slot, src, inv) :: rest, sc, z, nz, k => by
    simp only [osBasisRow]
    obtain ⟨n1, n2⟩ := osBasisBlk_next bd slot src inv sc z nz k
    obtain ⟨r1, r2⟩ := osBasisRow_next bd rest (osBasisBlk bd slot src inv sc z nz k).2.1 z nz
      (osBasisBlk bd slot src inv sc z nz k).2.2
    refine ⟨by omega, fun _ ↦ ?_⟩
    rcases rest with _ | ⟨c2, rest⟩
    · simp only [osBasisRow]; exact n2
    · exact r2 (by simp)

/-- **A basis row, honestly**: from the scale `sc`, at the zero flag `zv`, every coordinate `t`
reading `cv t` at its source and storing its `d`. -/
theorem osBasisRow_complete {bd z nz : ℕ} {zv : E} (cv : ℕ → E) :
    ∀ (cs : List (ℕ × (ℕ × ℕ) × ℕ)) (sc : ℕ) (k : ℕ) (σ : Val),
      bd < k → sc < k → z < k → nz < k → σ (.n z) = zv → σ (.n nz) = 1 + zv →
      (∀ t < cs.length, (cs.getD t coordD).2.1.1 < k ∧
        cv t * word (cs.getD t coordD).2.2 0 * (1 + zv) + zv ≠ 0 ∧ ∀ C rd, HM M H C rd →
          LoadHolds rd (σ (.n (cs.getD t coordD).2.1.1)) (cs.getD t coordD).2.1.2 (cv t) ∧
          LoadHolds rd (σ (.n bd)) (cs.getD t coordD).1
            (dZv (cv t) (word (cs.getD t coordD).2.2 0) zv)) →
      BlkA M H σ k (osBasisRow bd cs sc z nz k).2.2 (osBasisRow bd cs sc z nz k).1
        (fun σ' ↦ σ' (.n (osBasisRow bd cs sc z nz k).2.1) =
            σ' (.n sc) * ∏ t ∈ Finset.range cs.length, (cv t * word (cs.getD t coordD).2.2 0))
  | [], sc, k, σ, _, _, _, _, _, _, _ => BlkA.nil fun σ' _ ↦ by simp [osBasisRow]
  | (slot, src, inv) :: rest, sc, k, σ, hbd, hsc, hz, hnz, hzv, hnzv, hin => by
    obtain ⟨h0s, h0n, h0m⟩ := hin 0 (by simp)
    simp only [List.getD_cons_zero] at h0s h0n h0m
    have hA := osBasisBlk_complete (M := M) (H := H) (bd := bd) (slot := slot) (inv := inv) (sc := sc)
      (k := k) (src := src) (cv := cv 0) h0s hbd hsc hz hnz hzv hnzv h0n
      (fun C rd hH ↦ (h0m C rd hH).1) (fun C rd hH ↦ (h0m C rd hH).2)
    obtain ⟨n1, n2⟩ := osBasisBlk_next bd slot src inv sc z nz k
    set r := osBasisBlk bd slot src inv sc z nz k with hr
    have hB := BlkA.seq (M := M) (H := H) (by omega) (osBasisRow_next bd rest r.2.1 z nz r.2.2).1
      hA.agree fun σ1 ha1 _ ↦ osBasisRow_complete (bd := bd) (z := z) (nz := nz) (zv := zv)
        (fun t ↦ cv (t + 1)) rest r.2.1 r.2.2 σ1
        (by omega) n2 (by omega) (by omega) (by rw [ha1 _ hz]; exact hzv)
        (by rw [ha1 _ hnz]; exact hnzv) fun t ht ↦ by
          obtain ⟨a, b, m⟩ := hin (t + 1) (by simp; omega)
          simp only [List.getD_cons_succ] at a b m
          refine ⟨by omega, b, fun C rd hH ↦ ?_⟩
          obtain ⟨m1, m2⟩ := m C rd hH
          rw [← ha1 _ a] at m1
          rw [← ha1 _ hbd] at m2
          exact ⟨m1, m2⟩
    simp only [osBasisRow]
    refine hB.mono fun σ' ⟨⟨o1, ha⟩, o3⟩ ↦ ?_
    rw [o3, o1, ha _ hsc, List.length_cons, Finset.prod_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-! ## A level's row -/

theorem osBasisLv_next (c : OsCfg) (tch bd ls la lvl : ℕ) (lv : OsLv) (k : ℕ) :
    k ≤ (osBasisLv c tch bd ls la lvl lv k).2 := by
  unfold osBasisLv
  dsimp only
  have h1 := (osAfterRow_next ((osBasisCoords c tch lvl lv).map (·.2.1)) none (k + 1)).1
  have h2 := (osBasisRow_next bd (osBasisCoords c tch lvl lv) k
    (osAfterRow ((osBasisCoords c tch lvl lv).map (·.2.1)) none (k + 1)).2.2
    ((osAfterRow ((osBasisCoords c tch lvl lv).map (·.2.1)) none (k + 1)).2.2 + 2)
    ((osAfterRow ((osBasisCoords c tch lvl lv).map (·.2.1)) none (k + 1)).2.2 + 3)).1
  omega

theorem osBases_next (c : OsCfg) (tch bd ls la : ℕ) :
    ∀ (lvs : List OsLv) (lvl k : ℕ), k ≤ (osBases c tch bd ls la lvl lvs k).2
  | [], _, _ => le_rfl
  | lv :: rest, lvl, k => by
    simp only [osBases]
    exact le_trans (osBasisLv_next c tch bd ls la lvl lv k)
      (osBases_next c tch bd ls la rest (lvl + 1) _)

theorem coordSrc_lt {tch : ℕ} {lv : OsLv} {t k : ℕ} (hf : osFch < k) (ht : tch < k) :
    (coordSrc tch lv t).1 < k := by
  unfold coordSrc; split_ifs <;> assumption

theorem basisIn_agree {rd : Reader} {σ σ' : Val} {c : OsCfg} {tch L k : ℕ} {lv : OsLv} {β : E}
    {X : ℕ → E} (hk : 43 ≤ k) (htch : tch < k) (ha : AgreeBelow k σ σ')
    (h : BasisIn rd σ c tch L lv β X) : BasisIn rd σ' c tch L lv β X := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rwa [ha _ (by show 20 < k; omega)], fun t ht ↦ ⟨(h2 t ht).1, ?_⟩⟩
  rw [ha _ (coordSrc_lt (by show 16 < k; omega) htch)]
  exact (h2 t ht).2

theorem basisOut_agree {rd : Reader} {σ σ' : Val} {c : OsCfg} {bd ls la L k : ℕ} {lv : OsLv} {β : E}
    {X : ℕ → E} (hbd : bd < k) (hls : ls < k) (hla : la < k) (ha : AgreeBelow k σ σ')
    (h : BasisOut rd σ c bd ls la L lv β X) : BasisOut rd σ' c bd ls la L lv β X := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨fun t ht ↦ by rw [ha _ hbd]; exact h1 t ht, by rwa [ha _ hls], by rwa [ha _ hla]⟩

theorem osAfterRow_calls : ∀ srcs prev k, (osAfterRow srcs prev k).1.filterMap callVs = []
  | [], _, _ => rfl
  | _ :: rest, none, k => by
    simp only [osAfterRow, List.filterMap_cons, osAfterRow_calls rest]; rfl
  | _ :: rest, some _, k => by
    simp only [osAfterRow, List.filterMap_cons, osAfterRow_calls rest]; rfl

theorem osBasisRow_calls (bd : ℕ) : ∀ cs sc z nz k, (osBasisRow bd cs sc z nz k).1.filterMap callVs = []
  | [], _, _, _, _ => rfl
  | (slot, src, inv) :: rest, sc, z, nz, k => by
    simp only [osBasisRow, calls_append, osBasisRow_calls bd rest, List.append_nil]
    unfold osBasisBlk; dsimp only
    split_ifs <;> rfl

/-- The non-final levels' basis rows' calls' values: each row's `is_zero` of the product of its
coordinates `X lvl`. -/
def basesCV (c : OsCfg) (X : ℕ → ℕ → E) : List OsLv → ℕ → List (List E)
  | [], _ => []
  | lv :: rest, lvl => [∏ t ∈ Finset.range (lv.prefixLen + c.yrLog), X lvl t,
      zeroOf (∏ t ∈ Finset.range (lv.prefixLen + c.yrLog), X lvl t)] :: basesCV c X rest (lvl + 1)

/-- **A non-final level's basis row, honestly**: on memory holding what it reads (`BasisIn`) and
what it stores (`BasisOut`). -/
theorem osBasisLv_complete {c : OsCfg} {tch bd ls la lvl : ℕ} {lv : OsLv} {k : ℕ} {σ : Val}
    {β : E} {X : ℕ → E} (hiz : IsZeroC (HM M H)) (hpos : 1 ≤ lv.prefixLen + c.yrLog)
    (hbd : bd < k) (hls : ls < k) (hla : la < k) (htch : tch < k) (hk : 43 ≤ k)
    (hm : ∀ C rd, HM M H C rd → BasisIn rd σ c tch lvl lv β X ∧ BasisOut rd σ c bd ls la lvl lv β X) :
    BlkA M H σ k (osBasisLv c tch bd ls la lvl lv k).2 (osBasisLv c tch bd ls la lvl lv k).1
      (fun σ' ↦ cvOf (osBasisLv c tch bd ls la lvl lv k).1 σ' =
        [[∏ t ∈ Finset.range (lv.prefixLen + c.yrLog), X t,
          zeroOf (∏ t ∈ Finset.range (lv.prefixLen + c.yrLog), X t)]]) := by
  set n := lv.prefixLen + c.yrLog with hn
  have hlen : (osBasisCoords c tch lvl lv).length = n := by simp [osBasisCoords, n]
  have hcs : ∀ t < n, (osBasisCoords c tch lvl lv).getD t coordD =
      (lvl * ligColsCap + t, coordSrc tch lv t, vanishInv (lv.vanish + t)) :=
    fun t ht ↦ osBasisCoords_getD ht
  unfold osBasisLv
  dsimp only
  set cs := osBasisCoords c tch lvl lv with hcsd
  set af := osAfterRow (cs.map (·.2.1)) none (k + 1) with haf
  set P := ∏ t ∈ Finset.range n, X t with hP
  have hne : cs ≠ [] := by intro h0; rw [← hlen, h0] at hpos; simp at hpos
  obtain ⟨haf1, haf2⟩ := osAfterRow_next (cs.map (·.2.1)) none (k + 1)
  have haz : af.2.1.getD 0 < af.2.2 := by
    rcases haf2 with h | ⟨b, hb, -, h2⟩
    · exfalso
      have := osAfterRow_isSome (cs.map (·.2.1)) none (k + 1) (Or.inr (by simpa using hne))
      rw [← haf, h] at this
      simp at this
    · rw [hb]; exact h2
  set a := af.2.1.getD 0 with hadef
  set z := af.2.2 with hz
  obtain ⟨hr1, hr2⟩ := osBasisRow_next bd cs k z (z + 2) (z + 3)
  have hr2 := hr2 hne
  set r := osBasisRow bd cs k z (z + 2) (z + 3) with hr
  -- β
  have hL : BlkA M H σ k (k + 1) [osLd k osBetas lvl] (fun σ' ↦ σ' (.n k) = β) :=
    blk_lst [β] (by simp) fun C rd hH σ' ha hv ↦ by
      have v0 := hv 0 (by simp)
      simp only [List.getD_cons_zero, Nat.add_zero] at v0
      simp only [osLd, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load]
      rw [v0, ha _ (by show 20 < k; omega)]
      exact ⟨(hm C rd hH).1.1, rfl⟩
  -- the product
  have hA := BlkA.seq (M := M) (H := H) (by omega) haf1 hL.agree fun σ1 ha1 _ ↦
    osAfterRow_complete (M := M) (H := H) X (cs.map (·.2.1)) none (k + 1) σ1 (fun x hx ↦ by simp at hx)
      fun t ht ↦ by
        rw [List.length_map, hlen] at ht
        have e : (cs.map (·.2.1)).getD t (0, 0) = coordSrc tch lv t := by
          rw [List.getD_eq_getElem _ _ (by simp [hlen]; exact ht), List.getElem_map,
            ← List.getD_eq_getElem _ coordD (by rw [hlen]; exact ht), hcs t ht]
        rw [e]
        refine ⟨coordSrc_lt (by show 16 < k + 1; omega) (by omega), fun C rd hH ↦ ?_⟩
        rw [ha1 _ (coordSrc_lt (by show 16 < k; omega) htch)]
        exact ((hm C rd hH).1.2 t ht).2
  -- the flag
  have hZ := BlkA.seq (M := M) (H := H) (show k ≤ z by omega) (show z ≤ z + 3 by omega) hA.agree
    (B := [.call "is_zero" [.n a] [.n z], osCst (z + 1) (word 1 0), osAdd (z + 2) (z + 1) z])
    (OutB := fun σ' ↦ σ' (.n z) = zeroOf P ∧ σ' (.n (z + 2)) = 1 + zeroOf P) fun σ1 ha1 ho1 ↦
      blk_lst [zeroOf P, word 1 0, word 1 0 + zeroOf P] (by simp) fun C rd hH σ' ha hv ↦ by
        have v0 := hv 0 (by simp)
        have v1 := hv 1 (by simp)
        have v2 := hv 2 (by simp)
        simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2
        have hav : σ' (.n a) = P := by
          obtain ⟨⟨-, o2⟩, -⟩ := ho1 C rd hH
          rw [ha _ haz]
          have := o2 (Or.inr (by simpa [hlen] using hne))
          simpa [optVal, hlen] using this
        simp only [osCst, osAdd, allOk_cons, allOk_nil, and_true, stmtOk_atom, stmtOk_call,
          holds_const, holds_add, List.map_cons, List.map_nil]
        rw [v0, v1, v2, hav, word_one]
        exact ⟨⟨hiz C rd hH P, rfl, rfl⟩, rfl, rfl⟩
  -- the row
  have hR := BlkA.seq (M := M) (H := H) (show k ≤ z + 3 by omega) hr1 hZ.agree fun σ2 ha2 ho2 ↦
    BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ by
      obtain ⟨⟨-, e0, e2⟩, -⟩ := ho2 C0 rd0 hH0
      have hk2 : AgreeBelow k σ σ2 := fun i hi ↦ ha2 i (by omega)
      refine osBasisRow_complete (M := M) (H := H) (bd := bd) (z := z) (nz := z + 2) (zv := zeroOf P) X cs k
        (z + 3) σ2 (by omega) (by omega) (by omega) (by omega) e0 e2 fun t ht ↦ ?_
      rw [hlen] at ht
      rw [hcs t ht]
      refine ⟨coordSrc_lt (by show 16 < z + 3; omega) (by omega), coef_div_ne ?_, fun C rd hH ↦ ?_⟩
      · by_cases h0 : P = 0
        · exact Or.inr (zeroOf_eq_one h0)
        · exact Or.inl ⟨zeroOf_eq_zero h0,
            mul_ne_zero (prod_ne_factor h0 ht) ((hm C0 rd0 hH0).1.2 t ht).1⟩
      · obtain ⟨⟨-, hx⟩, ⟨hd, -⟩⟩ := hm C rd hH
        rw [hk2 _ (coordSrc_lt (by show 16 < k; omega) htch), hk2 _ hbd]
        exact ⟨(hx t ht).2, hd t ht⟩
  -- the scale and the product stored
  have hS := BlkA.seq (M := M) (H := H) (show k ≤ r.2.2 by omega) (le_refl r.2.2) hR.agree
    (B := [osLd r.2.1 ls lvl, osLd a la lvl]) (OutB := fun _ ↦ True) fun σ3 ha3 ho3 ↦
      blk_lst [] (by simp) fun C rd hH σ' ha _ ↦ by
        obtain ⟨⟨⟨⟨⟨⟨⟨eb, -⟩, eaf⟩, -⟩, -⟩, -⟩, er⟩, -⟩ := ho3 C rd hH
        obtain ⟨-, -, s1, s2⟩ := hm C rd hH
        have hav : σ3 (.n a) = P := by
          have := eaf (Or.inr (by simpa [hlen] using hne))
          simpa [optVal, hlen] using this
        simp only [osLd, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load]
        rw [ha _ hr2, ha _ (show a < r.2.2 by omega), ha _ (show ls < r.2.2 by omega),
          ha _ (show la < r.2.2 by omega), er, hav, ha3 _ hls, ha3 _ hla, eb]
        have hprod : ∏ t ∈ Finset.range cs.length, (X t * word (cs.getD t coordD).2.2 0) =
            ∏ t ∈ Finset.range n, (X t * invW lv t) := by
          rw [hlen]
          exact Finset.prod_congr rfl fun t ht ↦ by rw [hcs t (Finset.mem_range.mp ht)]
        rw [hprod]
        exact ⟨s1, s2⟩
  rw [← haf, ← hr] at hS
  refine (hS.congr ?_).mono fun σ' ho ↦ ?_
  · simp only [List.cons_append, List.append_assoc, List.nil_append]
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, eaf⟩, -⟩, ez, -⟩, -⟩, -⟩, -⟩, -⟩ := ho
  have hav : σ' (.n a) = P := by
    have := eaf (Or.inr (by simpa [hlen] using hne))
    simpa [optVal, hlen] using this
  have c1 : af.1.filterMap callVs = [] := osAfterRow_calls _ _ _
  have c2 : r.1.filterMap callVs = [] := osBasisRow_calls _ _ _ _ _ _
  rw [cvOf]
  simp only [List.filterMap_cons, List.filterMap_append, c1, c2, List.filterMap_nil, callVs, osLd,
    osCst, osAdd, List.nil_append, List.append_nil, List.cons_append, List.map_cons, List.map_nil, hav, ez]

/-- **Every non-final level's basis row, honestly**: on memory holding what each row reads
(`BasisIn`) and what it stores (`BasisOut`). -/
theorem osBases_complete {c : OsCfg} {tch bd ls la : ℕ} (β : ℕ → E) (X : ℕ → ℕ → E)
    (hiz : IsZeroC (HM M H)) (hpos : ∀ lv : OsLv, 1 ≤ lv.prefixLen + c.yrLog) :
    ∀ (levels : List OsLv) (lvl k : ℕ) (σ : Val), bd < k → ls < k → la < k → tch < k → 43 ≤ k →
      (∀ i (hi : i < levels.length), ∀ C rd, HM M H C rd →
        BasisIn rd σ c tch (lvl + i) levels[i] (β (lvl + i)) (X (lvl + i)) ∧
          BasisOut rd σ c bd ls la (lvl + i) levels[i] (β (lvl + i)) (X (lvl + i))) →
      BlkA M H σ k (osBases c tch bd ls la lvl levels k).2 (osBases c tch bd ls la lvl levels k).1
        (fun σ' ↦ cvOf (osBases c tch bd ls la lvl levels k).1 σ' = basesCV c X levels lvl)
  | [], _, _, _, _, _, _, _, _, _ => BlkA.nil fun _ _ ↦ rfl
  | lv :: rest, lvl, k, σ, hbd, hls, hla, htch, hk, hm => by
    have hm0 := fun C rd hH ↦ hm 0 (by simp) C rd hH
    simp only [Nat.add_zero, List.getElem_cons_zero] at hm0
    have hA := osBasisLv_complete (M := M) (H := H) (lvl := lvl) (lv := lv) (k := k) (σ := σ) hiz (hpos lv)
      hbd hls hla htch hk hm0
    have hnx := osBases_next c tch bd ls la rest (lvl + 1) (osBasisLv c tch bd ls la lvl lv k).2
    have hk1 := osBasisLv_next c tch bd ls la lvl lv k
    have hall := BlkA.seq (M := M) (H := H) hk1 hnx hA.agree fun σ3 ha3 _ ↦
      osBases_complete β X hiz hpos rest (lvl + 1) _ σ3 (by omega) (by omega) (by omega) (by omega)
        (by omega) fun i hi C rd hH ↦ by
          have h := hm (i + 1) (by simp; omega) C rd hH
          simp only [List.getElem_cons_succ, show lvl + (i + 1) = lvl + 1 + i by ring] at h
          exact ⟨basisIn_agree (by omega) htch ha3 h.1, basisOut_agree hbd hls hla ha3 h.2⟩
    refine (hall.congr ?_).mono fun σ' ⟨⟨h1, _⟩, h2⟩ ↦ ?_
    · simp only [osBases]
    show cvOf (_ ++ _) σ' = _
    rw [cvOf_append, h1, h2]
    rfl

end
end LeanVM.Guest.B1.Whir
