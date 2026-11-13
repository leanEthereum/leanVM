/-
  LeanVM.Guest.B1.Gkr.Loop29

  `verify_bus_gkr`'s inner loop `verify_bus_gkr_loop0_loop0`: eight GKR rounds an iteration, from
  one round record to the record eight on.
-/

module

public import LeanVM.Guest.B1.Gkr.Rounds
public import LeanVM.Guest.Data.NameStrings

/-!
# `verify_bus_gkr_loop0_loop0` (G:1980-2001)

`for x8 in mul_range(1, half)` in a layer of `verify_bus_gkr`: the record at
`rd = rounds·pos·x8^8`, the point row `pt = point_row·x8^8`, eight rounds (`gkRoundT`, from values
`17 + 40q`), and the record at `rd·g^8` written. `l29_step`: an iteration is
`TbGkrRoundsOut 8` from its record; `l29_loop`: the loop from `g^0` to `half = g^h` is
`TbGkrRoundsOut (8h)` from the first record.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Round `q`'s first value. -/
def l29B (q : ℕ) : ℕ := 17 + 40 * q

/-- Round `q`'s claim. -/
def l29Claim (q : ℕ) : ℕ := 16 + 40 * q

/-- Round `q`'s capacity. -/
def l29Cap (q : ℕ) : List V :=
  if q = 0 then [.n 10, .n 11, .n 12, .n 13, .n 14]
  else (List.range 5).map fun k ↦ .n (l29B (q - 1) + 20 + k)

/-- `verify_bus_gkr_loop0_loop0`'s body. -/
def l29Body : List Stmt :=
  [.atom (.mul (.n 5) (.n 0) (.n 0)), .atom (.mul (.n 6) (.n 5) (.n 5)),
    .atom (.mul (.n 7) (.n 6) (.n 6)),
    .atom (.mul (.n 8) (.n 2) (.n 7)), .atom (.mul (.n 9) (.n 3) (.n 7)),
    .atom (.load (.n 10) (.n 8) 0), .atom (.load (.n 11) (.n 8) 862),
    .atom (.load (.n 12) (.n 8) 1724), .atom (.load (.n 13) (.n 8) 2586),
    .atom (.load (.n 14) (.n 8) 3448), .atom (.load (.n 15) (.n 8) 4310),
    .atom (.load (.n 16) (.n 8) 5172)] ++
  ((List.range 8).map fun q ↦ gkRoundT (l29B q) q (.n 15) (.n 9) (.n (l29Claim q)) (l29Cap q)).flatten ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (317 + k)) (.n 8) (8 + 862 * k))) ++
  [.atom (.const (.n 337) (word 4294967296 0)), .atom (.mul (.n 338) (.n 15) (.n 337)),
    .atom (.load (.n 338) (.n 8) 4318), .atom (.load (.n 336) (.n 8) 5180),
    .atom (.const (.n 339) (word 2 0)), .atom (.mul (.n 340) (.n 0) (.n 339)),
    .atom (.add (.n 341) (.n 340) (.n 1)), .atom (.const (.n 342) (word 2 0)),
    .atom (.mul (.n 343) (.n 0) (.n 342)),
    .callIf (.n 341) name% «verify_bus_gkr_loop0_loop0» [.n 343, .n 1, .n 2, .n 3, .n 4], .ret []]

noncomputable def l29Check : Bool :=
  match coreProgram.find? name% «verify_bus_gkr_loop0_loop0» with
  | some fn => decide (fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4]) && tbStmtsEqb fn.body l29Body
  | none => false

theorem l29Check_eq : l29Check = true := by decide +kernel

theorem l29Found : ∃ fn : Fn, coreProgram.find? name% «verify_bus_gkr_loop0_loop0» = some fn ∧
    fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4] ∧ fn.body = l29Body := by
  have h := l29Check_eq
  unfold l29Check at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, tbStmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

/-- One round of `gkrRun`, from what the guest's round gives. -/
theorem tb_gkrRun_cons_of {c : List E} {cs : List (List E)} {e : E} {es : List E} {claim ch : E}
    {cap cap' : List E} (hch : ch = ((⟨cap, []⟩ : Fs).absorbAll c dsObserve).squeeze.1)
    (hcap : cap' = ((⟨cap, []⟩ : Fs).absorbAll c dsObserve).squeeze.2.cap) :
    gkrRun (c :: cs) (e :: es) claim ⟨cap, []⟩ =
      (ch :: (gkrRun cs es (polyEval ((claim + e * sumE c) :: c) ch) ⟨cap', []⟩).1,
        (gkrRun cs es (polyEval ((claim + e * sumE c) :: c) ch) ⟨cap', []⟩).2) := by
  subst hch hcap
  rfl

section Sem

variable {rd : Reader}

theorem l29_round_cap (q : ℕ) (σ : Val) :
    (l29Cap (q + 1)).map σ = (List.range 5).map fun k ↦ σ (.n (l29B q + 20 + k)) := by
  simp [l29Cap]

/-- **An iteration of `verify_bus_gkr_loop0_loop0`**: eight rounds from the record at `head·x^8`. -/
theorem l29_step {N head ptrow tabs : E} (d : ℕ) (x : E)
    (h : coreProgram.relN rd (d + 1) name% «verify_bus_gkr_loop0_loop0» (x :: [N, head, ptrow,
        tabs]) []) :
    TbGkrRoundsOut 8 rd (head * x ^ 8) (ptrow * x ^ 8) ∧
      (x * gen + N ≠ 0 → coreProgram.relN rd d name% «verify_bus_gkr_loop0_loop0» (x * gen :: [N,
          head, ptrow, tabs]) []) := by
  obtain ⟨fn, hf, σ, hpar, hbody⟩ := h
  obtain ⟨fn', hf', hp, hb⟩ := l29Found
  rw [hf] at hf'
  obtain rfl := Option.some.inj hf'
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hpar
  have nR := tb_noRetList_flatten_range 8 (fun q ↦ gkRoundT (l29B q) q (.n 15) (.n 9)
    (.n (l29Claim q)) (l29Cap q)) (fun q => gkRoundT_noRet _ _ _ _ _ _)
  rw [hb, l29Body, holdsList_append, holdsList_noRet _ (by
      simp only [tb_noRetList_append, nR, tb_noRetList_mapAtoms]; rfl),
    tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nR]; rfl),
    tb_holdsList_append_noRet (by rfl), tb_holdsList_flatten_range _ _ (fun q =>
      gkRoundT_noRet _ _ _ _ _ _), tb_holdsList_mapAtoms] at hbody
  obtain ⟨⟨⟨hh, hrounds⟩, hst⟩, htl⟩ := hbody
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, List.map_cons, List.map_nil] at hh htl
  obtain ⟨h5, h6, h7, h8, h9, l10, l11, l12, l13, l14, l15, l16⟩ := hh
  obtain ⟨c337, m338, s338, s336, c339, m340, a341, c342, m343, -, hnext⟩ := htl
  refine ⟨?_, fun hne => ?_⟩
  swap
  · have := hnext (by rw [a341, m340, c339, tb_word_gen]; exact hne)
    rw [m343, c342, tb_word_gen] at this
    exact this
  have R := fun q (hq : q < 8) => holds_gkRound (hrounds q hq)
  obtain ⟨xs0, hx0, hr0, hc0, hcap0, hs0, e0, he0, hcl0⟩ := R 0 (by norm_num)
  obtain ⟨xs1, hx1, hr1, hc1, hcap1, hs1, e1, he1, hcl1⟩ := R 1 (by norm_num)
  obtain ⟨xs2, hx2, hr2, hc2, hcap2, hs2, e2, he2, hcl2⟩ := R 2 (by norm_num)
  obtain ⟨xs3, hx3, hr3, hc3, hcap3, hs3, e3, he3, hcl3⟩ := R 3 (by norm_num)
  obtain ⟨xs4, hx4, hr4, hc4, hcap4, hs4, e4, he4, hcl4⟩ := R 4 (by norm_num)
  obtain ⟨xs5, hx5, hr5, hc5, hcap5, hs5, e5, he5, hcl5⟩ := R 5 (by norm_num)
  obtain ⟨xs6, hx6, hr6, hc6, hcap6, hs6, e6, he6, hcl6⟩ := R 6 (by norm_num)
  obtain ⟨xs7, hx7, hr7, hc7, hcap7, hs7, e7, he7, hcl7⟩ := R 7 (by norm_num)
  rw [l29_round_cap 0 σ] at hc1 hcap1
  rw [l29_round_cap 1 σ] at hc2 hcap2
  rw [l29_round_cap 2 σ] at hc3 hcap3
  rw [l29_round_cap 3 σ] at hc4 hcap4
  rw [l29_round_cap 4 σ] at hc5 hcap5
  rw [l29_round_cap 5 σ] at hc6 hcap6
  rw [l29_round_cap 6 σ] at hc7 hcap7
  have ecap0 : (l29Cap 0).map σ = [σ (.n 10), σ (.n 11), σ (.n 12), σ (.n 13), σ (.n 14)] := rfl
  rw [ecap0] at hc0 hcap0
  simp only [l29B, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd,
    Nat.reduceMul] at hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hcap0 hcap1 hcap2 hcap3 hcap4 hcap5 hcap6 hcap7
  simp only [l29B, l29Claim, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd,
    Nat.reduceMul] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hcl0 hcl1 hcl2 hcl3 hcl4 hcl5 hcl6 hcl7
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
  -- the run
  have hrun : gkrRun [xs0, xs1, xs2, xs3, xs4, xs5, xs6, xs7] [e0, e1, e2, e3, e4, e5, e6, e7] (σ (.n 16))
      ⟨[σ (.n 10), σ (.n 11), σ (.n 12), σ (.n 13), σ (.n 14)], []⟩ =
      ([σ (.n 42), σ (.n 82), σ (.n 122), σ (.n 162), σ (.n 202), σ (.n 242), σ (.n 282), σ (.n 322)], σ (.n 336),
        ⟨(List.range 5).map fun k ↦ σ (.n (317 + k)), []⟩) := by
    rw [tb_gkrRun_cons_of hc0 hcap0, ← hcl0, tb_gkrRun_cons_of hc1 hcap1, ← hcl1, tb_gkrRun_cons_of hc2 hcap2, ← hcl2, tb_gkrRun_cons_of hc3 hcap3, ← hcl3, tb_gkrRun_cons_of hc4 hcap4, ← hcl4, tb_gkrRun_cons_of hc5 hcap5, ← hcl5, tb_gkrRun_cons_of hc6 hcap6, ← hcl6, tb_gkrRun_cons_of hc7 hcap7, ← hcl7]
    simp [gkrRun]
  have hl4 : ∀ l : List E, l.length = 4 → ∃ a b c d, l = [a, b, c, d] := fun l hl => by
    match l, hl with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  obtain ⟨a0, b0, c0, d0, rfl⟩ := hl4 xs0 hx0
  obtain ⟨a1, b1, c1, d1, rfl⟩ := hl4 xs1 hx1
  obtain ⟨a2, b2, c2, d2, rfl⟩ := hl4 xs2 hx2
  obtain ⟨a3, b3, c3, d3, rfl⟩ := hl4 xs3 hx3
  obtain ⟨a4, b4, c4, d4, rfl⟩ := hl4 xs4 hx4
  obtain ⟨a5, b5, c5, d5, rfl⟩ := hl4 xs5 hx5
  obtain ⟨a6, b6, c6, d6, rfl⟩ := hl4 xs6 hx6
  obtain ⟨a7, b7, c7, d7, rfl⟩ := hl4 xs7 hx7
  have q8 : σ (.n 8) = σ (.n 2) * σ (.n 0) ^ 8 := by rw [h8, h7, h6, h5]; ring
  have q9 : σ (.n 9) = σ (.n 3) * σ (.n 0) ^ 8 := by rw [h9, h7, h6, h5]; ring
  rw [← q8, ← q9]
  refine ⟨[σ (.n 10), σ (.n 11), σ (.n 12), σ (.n 13), σ (.n 14)], σ (.n 15), σ (.n 16),
    [[a0, b0, c0, d0], [a1, b1, c1, d1], [a2, b2, c2, d2], [a3, b3, c3, d3], [a4, b4, c4, d4], [a5, b5, c5, d5], [a6, b6, c6, d6], [a7, b7, c7, d7]], [e0, e1, e2, e3, e4, e5, e6, e7],
    ⟨rfl, fun j hj => ?_⟩, l15, l16, rfl, by simp, fun k hk => ?_, rfl, fun k hk => ?_, ?_,
    ⟨by rw [hrun]; simp, fun j hj => ?_⟩, ?_, ?_⟩
  · have hj' : j < 5 := hj
    interval_cases j
    · exact l10
    · exact l11
    · exact l12
    · exact l13
    · exact l14
  · simp only [List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
      List.append_nil, List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact hr0 0 (by omega)
    · exact hr0 1 (by omega)
    · exact hr0 2 (by omega)
    · exact hr0 3 (by omega)
    · exact hr1 0 (by omega)
    · exact hr1 1 (by omega)
    · exact hr1 2 (by omega)
    · exact hr1 3 (by omega)
    · exact hr2 0 (by omega)
    · exact hr2 1 (by omega)
    · exact hr2 2 (by omega)
    · exact hr2 3 (by omega)
    · exact hr3 0 (by omega)
    · exact hr3 1 (by omega)
    · exact hr3 2 (by omega)
    · exact hr3 3 (by omega)
    · exact hr4 0 (by omega)
    · exact hr4 1 (by omega)
    · exact hr4 2 (by omega)
    · exact hr4 3 (by omega)
    · exact hr5 0 (by omega)
    · exact hr5 1 (by omega)
    · exact hr5 2 (by omega)
    · exact hr5 3 (by omega)
    · exact hr6 0 (by omega)
    · exact hr6 1 (by omega)
    · exact hr6 2 (by omega)
    · exact hr6 3 (by omega)
    · exact hr7 0 (by omega)
    · exact hr7 1 (by omega)
    · exact hr7 2 (by omega)
    · exact hr7 3 (by omega)
  · simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · simpa using he0
    · simpa using he1
    · simpa using he2
    · simpa using he3
    · simpa using he4
    · simpa using he5
    · simpa using he6
    · simpa using he7
  · rw [hrun]
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    rw [tb_loadHolds_mul_gen_pow]
    interval_cases k
    · simpa using hs0
    · simpa using hs1
    · simpa using hs2
    · simpa using hs3
    · simpa using hs4
    · simpa using hs5
    · simpa using hs6
    · simpa using hs7
  · generalize hR : gkrRun [[a0, b0, c0, d0], [a1, b1, c1, d1], [a2, b2, c2, d2], [a3, b3, c3, d3], [a4, b4, c4, d4], [a5, b5, c5, d5], [a6, b6, c6, d6], [a7, b7, c7, d7]] [e0, e1, e2, e3, e4, e5, e6, e7] (σ (.n 16))
      ⟨[σ (.n 10), σ (.n 11), σ (.n 12), σ (.n 13), σ (.n 14)], []⟩ = R at hj ⊢
    rw [hrun] at hR
    subst hR
    simp only [List.length_map, List.length_range] at hj
    have := hst j hj
    simp only [Atom.Holds] at this
    simpa [gkCap, Nat.mul_comm] using this
  · rw [show σ (.n 15) * gen ^ (4 * 8) = σ (.n 338) by
      rw [m338, c337, show (4294967296 : ℕ) = 2 ^ 32 by norm_num, tb_word_two_pow (by norm_num)]]
    exact s338
  · rw [hrun]
    exact s336

/-- No rounds: a record's facts. -/
theorem gkrRoundsOut_zero {rd : Reader} {rec pt : E} {cap : List E} {cur claim : E}
    (hc : TbCapAt rd rec 0 gkCap cap)
    (hcur : LoadHolds rd rec (5 * gkCap) cur) (hcl : LoadHolds rd rec (6 * gkCap) claim) :
    TbGkrRoundsOut 0 rd rec pt :=
  ⟨cap, cur, claim, [], [], hc, hcur, hcl, rfl, by simp, tbReadsAt_nil _ _, rfl,
    tbReadsAt_nil _ _, tbReadsAt_nil _ _, by simpa [gkrRun] using hc,
    by simpa using hcur, by simpa [gkrRun] using hcl⟩

/-- **`verify_bus_gkr_loop0_loop0` behind its guard**: from the record at `head`, `half = g^h`
iterations are the
`8h` rounds to the record at `head·g^(8h)`. -/
theorem l29_loop {rd : Reader} {half head ptrow tabs : E} {h : ℕ} (hh : half = gen ^ h)
    (hhb : h < 2 ^ 62)
    (hcall : 1 + half ≠ 0 → coreProgram.Rel rd name% «verify_bus_gkr_loop0_loop0» [1, half, head,
        ptrow, tabs] [])
    (h0 : TbGkrRoundsOut 0 rd head ptrow) : TbGkrRoundsOut (8 * h) rd head ptrow := by
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · simpa using h0
  have hne : 1 + half ≠ 0 := by
    rw [hh]
    intro h0'
    have := gen_pow_inj (by omega) (by decide) ((e_add_eq_zero_iff.mp h0').symm.trans
      (pow_zero gen).symm)
    omega
  have hrun := hcall hne
  rw [← pow_zero gen] at hrun
  obtain ⟨m, -, hN, hall⟩ := tb_loop_sound (B := fun x ↦ TbGkrRoundsOut 8 rd (head * x ^ 8)
    (ptrow * x ^ 8)) (fun d x hx => l29_step d x hx) 0 hrun
  have hmh : h ≤ m := by
    by_contra hc
    have := gen_pow_inj (by omega) (by omega) (hh.symm.trans hN)
    omega
  have key : ∀ i ≤ h, TbGkrRoundsOut (8 * i) rd head ptrow := by
    intro i hi
    induction i with
    | zero => simpa using h0
    | succ i ih =>
      have hb := hall i (by omega) (by omega)
      rw [← pow_mul, mul_comm i 8] at hb
      rw [show 8 * (i + 1) = 8 * i + 8 by ring]
      exact gkrRoundsOut_append (ih (by omega)) hb
  exact key h le_rfl

end Sem

end
end LeanVM.Guest.B1.Tables
