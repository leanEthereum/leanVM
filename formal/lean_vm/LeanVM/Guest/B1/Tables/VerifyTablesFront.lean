/-
  LeanVM.Guest.B1.Tables.VerifyTablesFront

  `verify_tables`' framework values: the index multilinear extensions of the memory and the
  bytecode blocks, and the five framework claims read from the stream.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesSel

/-!
# The framework values (G:1604-1631)

`verify_tables` stores `INDEX_MLE_FACTORS[t] = 1 + g^(2^t)` (`vt_idxc`), and for the memory and
the bytecode push blocks runs `idx_chain[x·g] = idx_chain[x]·(1 + zeta[x]·factor[x])` over the
block's log-height (`__loop14`, `__loop16`): the chain's end is `indexMle` of the point's first
coordinates (`vt_idx`). It reads the memory's three limbs and the two final counters from the
stream (`vt_fresh`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `INDEX_MLE_FACTORS` -/

theorem vt_idxc_blocks : ∀ t < 34, stmtsEqb
    [.atom (.const (.n (1818 + t)) (word (kToNat (1 + gpowK (2 ^ t))) 0 0)),
      .atom (.load (.n (1818 + t)) (.n 1817) t)] ((vtPre.drop (1506 + 2 * t)).take 2) = true := by
  decide +kernel

theorem vt_idxc {rd : Reader} {σ : Val} (h : VtHolds rd σ) :
    ∀ t < 34, LoadHolds rd (σ (.n 1817)) t (1 + gen ^ 2 ^ t) := by
  intro t ht
  obtain ⟨k, hb⟩ := h.slice _ _ (vt_idxc_blocks t ht)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hb
  obtain ⟨c, l⟩ := hb
  rw [c, word_ofK, ofBits_kToNat, ofK_add', ofK_one, gpowK_eq (by unfold u128Bound; exact Nat.pow_lt_pow_right (by decide) (by omega)),
    ← gen_pow_eq_ofK] at l
  exact l

/-! ## The index loops -/

/-- An index loop's statements before its `ret`, its own name `self`. -/
def idxPre (self : String) : List Stmt :=
  [.atom (.mul (.n 5) (.n 2) (.n 0)), .atom (.load (.n 6) (.n 5) 0),
    .atom (.const (.n 7) (word 1 0 0)), .atom (.mul (.n 8) (.n 3) (.n 0)),
    .atom (.load (.n 9) (.n 8) 0), .atom (.mul (.n 10) (.n 4) (.n 0)),
    .atom (.load (.n 11) (.n 10) 0), .atom (.mul (.n 12) (.n 9) (.n 11)),
    .atom (.add (.n 13) (.n 7) (.n 12)), .atom (.mul (.n 14) (.n 6) (.n 13)),
    .atom (.mul (.n 15) (.n 2) (.n 0)), .atom (.load (.n 14) (.n 15) 1),
    .atom (.const (.n 16) (word 2 0 0)), .atom (.mul (.n 17) (.n 0) (.n 16)),
    .atom (.add (.n 18) (.n 17) (.n 1)), .atom (.const (.n 19) (word 2 0 0)),
    .atom (.mul (.n 20) (.n 0) (.n 19)), .callIf (.n 18) self [.n 20, .n 1, .n 2, .n 3, .n 4]]

/-- An index loop's shape. -/
noncomputable def idxOk (self : String) : Bool :=
  match coreProgram.find? self with
  | some f => decide (f.params = [.n 0, .n 1, .n 2, .n 3, .n 4]) &&
      stmtsEqb f.body (idxPre self ++ [.ret []])
  | none => false

theorem idx_ok : idxOk "__loop14" = true ∧ idxOk "__loop16" = true := by decide +kernel

theorem idx_step {rd : Reader} {self : String} (hok : idxOk self = true) {x N ch z fac : E}
    (h : coreProgram.Rel rd self [x, N, ch, z, fac] []) :
    (∃ c zt ft, LoadHolds rd (ch * x) 0 c ∧ LoadHolds rd (z * x) 0 zt ∧
      LoadHolds rd (fac * x) 0 ft ∧ LoadHolds rd (ch * x) 1 (c * (1 + zt * ft))) ∧
      (x * gen + N ≠ 0 → coreProgram.Rel rd self [x * gen, N, ch, z, fac] []) := by
  unfold idxOk at hok
  split at hok
  · next f hf =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hpar, hbody⟩ := hok
    have hnr : Stmt.noRetList (idxPre self) = true := by simp [idxPre, Stmt.noRetList, Stmt.noRet]
    obtain ⟨σ, hp, hb, -⟩ := rel_pre hf (stmtsEqb_sound hbody) hnr h
    simp only [hpar, List.map_cons, List.map_nil, List.cons.injEq] at hp
    obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := hp
    simp only [idxPre, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one, word_gen,
      List.map_cons, List.map_nil] at hb
    obtain ⟨a5, l6, c7, a8, l9, a10, l11, a12, a13, a14, a15, l14, c16, a17, a18, c19, a20, -,
      hc⟩ := hb
    refine ⟨⟨σ (.n 6), σ (.n 9), σ (.n 11), by rw [← a5]; exact l6, by rw [← a8]; exact l9,
      by rw [← a10]; exact l11, ?_⟩, fun hne => ?_⟩
    · rw [← a15]
      rw [a14, a13, a12, c7] at l14
      exact l14
    · have := hc (by rw [a18, a17, c16]; exact hne)
      rw [a20, c19] at this
      exact this
  · exact absurd hok (by simp)

theorem indexMleFrom_eq (zs : List E) : ∀ (j : ℕ) (acc : E),
    indexMleFrom (gen ^ 2 ^ j) zs acc =
      acc * ∏ t ∈ Finset.range zs.length, (1 + zs.getD t 0 * (1 + gen ^ 2 ^ (j + t))) := by
  induction zs with
  | nil => intro j acc; simp [indexMleFrom]
  | cons z zs ih =>
    intro j acc
    simp only [indexMleFrom, List.length_cons]
    rw [show (gen ^ 2 ^ j) ^ 2 = gen ^ 2 ^ (j + 1) by rw [← pow_mul, ← pow_succ], ih (j + 1),
      Finset.prod_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero]
    simp only [show ∀ t, j + 1 + t = j + (t + 1) from fun t => by ring]
    ring

/-- **`indexMle`** of a point, as the product of its index factors. -/
theorem indexMle_eq (zs : List E) :
    indexMle zs = ∏ t ∈ Finset.range zs.length, (1 + zs.getD t 0 * (1 + gen ^ 2 ^ t)) := by
  have := indexMleFrom_eq zs 0 1
  simp only [pow_zero, pow_one, one_mul, Nat.zero_add] at this
  exact this

/-- An index chain of a push framework block, from value `c`, over the block's `g^κ` at `kv`. -/
def idxT (c kv : ℕ) (self : String) (slot : ℕ) : List Stmt :=
  [.atom (.hint (.alloc (.n c) 42)), .atom (.const (.n (c + 1)) (word 1 0 0)),
    .atom (.load (.n (c + 1)) (.n c) 0), .atom (.const (.n (c + 2)) (word 1 0 0)),
    .atom (.add (.n (c + 3)) (.n (c + 2)) (.n kv)), .atom (.const (.n (c + 4)) (word 1 0 0)),
    .callIf (.n (c + 3)) self [.n (c + 4), .n kv, .n c, .n 5, .n 1817],
    .atom (.mul (.n (c + 5)) (.n c) (.n kv)), .atom (.load (.n (c + 6)) (.n (c + 5)) 0),
    .atom (.load (.n (c + 6)) (.n 1852) slot)]

theorem vt_idx_blocks : stmtsEqb (idxT 1925 1893 "__loop14" 1) ((vtPre.drop 1649).take 10) = true ∧
    stmtsEqb (idxT 2029 1997 "__loop16" 2) ((vtPre.drop 1757).take 10) = true := by
  decide +kernel

/-- **An index chain** (G:1622-1627): over `g^m` with `m` at most the point's length, its end is
`indexMle` of the point's first `m` coordinates, stored at `block_index_mle[slot]`. -/
theorem vt_idx_gen {rd : Reader} {σ : Val} (h : VtHolds rd σ) {n c kv slot : ℕ} {self : String}
    (hok : idxOk self = true) (heq : stmtsEqb (idxT c kv self slot) ((vtPre.drop n).take 10) = true)
    {m : ℕ} (hkm : σ (.n kv) = gen ^ m) (hm : m < 34) {point : List E}
    (hz : ReadsAt rd (σ (.n 5)) point) (hml : m ≤ point.length) :
    σ (.n (c + 6)) = indexMle (point.take m) ∧ LoadHolds rd (σ (.n 1852)) slot (σ (.n (c + 6))) := by
  obtain ⟨kr, hb⟩ := h.slice _ _ heq
  simp only [idxT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, true_and, word_one,
    List.map_cons, List.map_nil] at hb
  obtain ⟨c1, l1, c2, a3, c4, -, hloop, m5, l6, s6⟩ := hb
  have hidxc := vt_idxc h
  have hB := Main.loop_sound (B := fun x => ∃ c' zt ft, LoadHolds rd (σ (.n c) * x) 0 c' ∧
      LoadHolds rd (σ (.n 5) * x) 0 zt ∧ LoadHolds rd (σ (.n 1817) * x) 0 ft ∧
      LoadHolds rd (σ (.n c) * x) 1 (c' * (1 + zt * ft)))
    (ps := [σ (.n kv), σ (.n c), σ (.n 5), σ (.n 1817)]) (N := σ (.n kv)) (m := m)
    (by unfold ordG; omega) hkm (fun x hx => idx_step hok hx) (fun hne => by
      have := hloop (by rw [a3, c2]; exact hne)
      rw [c4] at this
      exact this)
  have hch : ∀ t ≤ m, LoadHolds rd (σ (.n c)) t
      (∏ j ∈ Finset.range t, (1 + point.getD j 0 * (1 + gen ^ 2 ^ j))) := by
    intro t ht
    induction t with
    | zero => simp only [Finset.range_zero, Finset.prod_empty]; rw [← c1]; exact l1
    | succ t ih =>
      obtain ⟨c', zt, ft, lc, lz, lf, lc1⟩ := hB t (by omega)
      rw [loadHolds_gen_pow_mul, Nat.add_zero] at lc lz lf
      rw [loadHolds_gen_pow_mul] at lc1
      rw [loadHolds_unique lc (ih (by omega)), loadHolds_unique lz (hz t (by omega)),
        loadHolds_unique lf (hidxc t (by omega)), ← List.getD_eq_getElem point 0 (by omega)] at lc1
      rw [Finset.prod_range_succ]
      exact lc1
  rw [m5, hkm, loadHolds_gen_pow_mul, Nat.add_zero] at l6
  have e6 := loadHolds_unique l6 (hch m le_rfl)
  refine ⟨?_, s6⟩
  rw [e6, indexMle_eq, List.length_take, Nat.min_eq_left hml]
  exact Finset.prod_congr rfl fun t ht => by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt (Finset.mem_range.mp ht)]

/-! ## The framework claims -/

/-- The five framework values read: the memory's limbs and the two final counters. -/
def freshWords (σ : Val) : List E := [σ (.n 1937), σ (.n 1955), σ (.n 1973), σ (.n 3359), σ (.n 3409)]

/-- **The framework claims' values** (G:1604-1612): from the state of `cv` in `(fs0, fs1)`, the
five words at the cursor, absorbed in order to the state at `(3422, 3423)`, stored in
`claim_pool[0 .. 4]` with their blocks' `g^κ` in `claim_cplen_g`. -/
theorem vt_fresh {rd : Reader} {σ : Val} (h : VtHolds rd σ) {cv : Digest}
    (hcv : (σ (.n 0), σ (.n 1)) = digestScalars cv) :
    ReadsAt rd (σ (.n 2)) (freshWords σ) ∧
      (σ (.n 3422), σ (.n 3423)) = digestScalars (obsAll cv (freshWords σ)) ∧
      ReadsAt rd (σ (.n 13)) (freshWords σ) ∧
      ReadsAt rd (σ (.n 14)) [σ (.n 1893), σ (.n 1893), σ (.n 1893), σ (.n 3345), σ (.n 3395)] := by
  have c19 := h.atom 0 (.copy (.n 19) (.n 0)) (by decide +kernel)
  have c20 := h.atom 1 (.copy (.n 20) (.n 1)) (by decide +kernel)
  obtain ⟨r0, f0⟩ := h.fsNext 1664 (.n 19) (.n 20) (.n 2) 0 1937 (by decide +kernel)
  obtain ⟨r1, f1⟩ := h.fsNext 1682 (.n 1950) (.n 1951) (.n 2) 1 1955 (by decide +kernel)
  obtain ⟨r2, f2⟩ := h.fsNext 1700 (.n 1968) (.n 1969) (.n 2) 2 1973 (by decide +kernel)
  obtain ⟨r3, f3⟩ := h.fsNext 3120 (.n 1986) (.n 1987) (.n 2) 3 3359 (by decide +kernel)
  obtain ⟨r4, f4⟩ := h.fsNext 3168 (.n 3372) (.n 3373) (.n 2) 4 3409 (by decide +kernel)
  have p0 := h.atom 1677 (.load (.n 1937) (.n 13) 0) (by decide +kernel)
  have p1 := h.atom 1695 (.load (.n 1955) (.n 13) 1) (by decide +kernel)
  have p2 := h.atom 1713 (.load (.n 1973) (.n 13) 2) (by decide +kernel)
  have p3 := h.atom 3133 (.load (.n 3359) (.n 13) 3) (by decide +kernel)
  have p4 := h.atom 3181 (.load (.n 3409) (.n 13) 4) (by decide +kernel)
  have q0 := h.atom 1678 (.load (.n 1893) (.n 14) 0) (by decide +kernel)
  have q1 := h.atom 1696 (.load (.n 1893) (.n 14) 1) (by decide +kernel)
  have q2 := h.atom 1714 (.load (.n 1893) (.n 14) 2) (by decide +kernel)
  have q3 := h.atom 3134 (.load (.n 3345) (.n 14) 3) (by decide +kernel)
  have q4 := h.atom 3182 (.load (.n 3395) (.n 14) 4) (by decide +kernel)
  simp only [Atom.Holds] at c19 c20 p0 p1 p2 p3 p4 q0 q1 q2 q3 q4
  simp only [Nat.reduceAdd] at f0 f1 f2 f3 f4
  have k0 := vt_fs_chain (show (σ (.n 19), σ (.n 20)) = digestScalars cv by rw [c19, c20]; exact hcv) f0
  have k1 := vt_fs_chain k0 f1
  have k2 := vt_fs_chain k1 f2
  have k3 := vt_fs_chain k2 f3
  have k4 := vt_fs_chain k3 f4
  refine ⟨fun k hk => ?_, k4, fun k hk => ?_, fun k hk => ?_⟩
  · simp only [freshWords, List.length_cons, List.length_nil] at hk
    interval_cases k
    exacts [r0, r1, r2, r3, r4]
  · simp only [freshWords, List.length_cons, List.length_nil] at hk
    interval_cases k
    exacts [p0, p1, p2, p3, p4]
  · simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    exacts [q0, q1, q2, q3, q4]

end
end LeanVM.Guest.B1.VerifySub
