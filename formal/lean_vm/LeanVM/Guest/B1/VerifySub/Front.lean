/-
  LeanVM.Guest.B1.VerifySub.Front

  `verify_sub`'s first phases as facts of its valuation: the seed, the announced sizes, the
  stack's root, the bus challenges.
-/

module

public import LeanVM.Guest.B1.VerifySub.Extract
public import LeanVM.Guest.B1.Log2

/-!
# The seed, the sizes, the root and the bus challenges (G:2091-2163)

Each lemma reads one phase of `verify_sub`'s body off a valuation satisfying it (`VsHolds`):

* `vs_seed`: `compress(seed, pi)` is `blake2sBytes (seed ‖ pi)` (G:2092-2093);
* `vs_reads`: the ten words read before the bus, `fs_next` each (`VsHolds.fsNext`), the six row
  counts stored at `table_rows`;
* `vs_rate`, `vs_logMem`: the rate's and the memory log's g-powers, range-checked
  (`g_power_of_word`, G:2108-2114);
* `vs_kappas`: `kappa_base` and `block_kappa` (G:2115-2123);
* `vs_challenges`: the four `alpha`s, `fp_w = eqKernel alphas`, `beta` (G:2144-2153).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## Blocks -/

/-- An `fs_next` block of the body: the word at the cursor's offset `j`, absorbed. -/
theorem VsHolds.fsNext (h : VsHolds rd σ) (n : ℕ) (s0 s1 cur : V) (j b : ℕ)
    (heq : stmtsEqb (fsNextT s0 s1 cur j b) ((vsPre.drop n).take 13) = true) :
    LoadHolds rd (σ cur) j (σ (.n b)) ∧ ∃ cv, (σ s0, σ s1) = digestScalars cv ∧
      (σ (.n (b + 13)), σ (.n (b + 14))) = digestScalars (obsCv cv (σ (.n b))) := by
  obtain ⟨⟨hl, cv, hcv, hv⟩, -⟩ := (holds_fsNextT (C := coreProgram.Rel rd) s0 s1 cur j b True _).mp
    (h.slice n _ (by rw [show (fsNextT s0 s1 cur j b).length = 13 by simp [fsNextT, fsCompressT]]; exact heq))
  refine ⟨hl, cv, hcv, ?_⟩
  have h12 := hv 12 (by omega) (by omega)
  have h13 := hv 13 (by omega) (by omega)
  rw [show b + 1 + 12 = b + 13 by omega] at h12
  rw [show b + 1 + 13 = b + 14 by omega] at h13
  rw [h12, h13, fsVals, fsVals, absorbCv_one]

/-- A `squeeze` block of the body: the new state and the challenge. -/
theorem VsHolds.squeeze (h : VsHolds rd σ) (n : ℕ) (s0 s1 : V) (b : ℕ)
    (heq : stmtsEqb (squeezeT s0 s1 b) ((vsPre.drop n).take 14) = true) :
    ∃ cv, (σ s0, σ s1) = digestScalars cv ∧
      (σ (.n (b + 5)), σ (.n (b + 6))) = digestScalars (sqCv cv) ∧
      σ (.n (b + 13)) = challengeOf (sqCv cv) := by
  obtain ⟨⟨cv, hcv, hv⟩, -⟩ := (holds_squeezeT (C := coreProgram.Rel rd) s0 s1 b True _).mp
    (h.slice n _ (by rw [show (squeezeT s0 s1 b).length = 14 by simp [squeezeT, squeezeStateT, challengeT]]; exact heq))
  refine ⟨cv, hcv, ?_, hv 13 (by omega)⟩
  rw [hv 5 (by omega), hv 6 (by omega)]
  simp only [sqVals, sqStateVals, absorbCv_sq]

/-! ## The seed -/

theorem vs_seed {N : ℕ} (h : VsHoldsTo N rd σ) (hN : 6 ≤ N) :
    ∃ seed pi : Digest, (σ (.n 2), σ (.n 3)) = digestScalars seed ∧
      (σ (.n 0), σ (.n 1)) = digestScalars pi ∧
      (σ (.n 12), σ (.n 13)) = digestScalars (blake2sBytes (digestBytes seed ++ digestBytes pi)) := by
  replace h := h.mono hN
  have hs := h.slice' 2 [.atom (.const (.n 9) (word 13503953895743350343 11912009169889063794 0)),
    .atom (.const (.n 10) (word 11170449402626986623 6620516960021240235 0)),
    .atom (.const (.n 11) (word 64 4294967295 0)),
    .atom (.blake2s (.n 2) (.n 3) (.n 0) (.n 1) (.n 9) (.n 10) (.n 12) (.n 13) (.n 11))]
    (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_iv0, word_iv1, word_md64, and_true] at hs
  obtain ⟨h9, h10, h11, hc⟩ := hs
  rw [h9, h10, h11] at hc
  obtain ⟨seed, hseed⟩ := exists_digest (hc.1 0) (hc.1 1)
  obtain ⟨pi, hpi⟩ := exists_digest (hc.1 2) (hc.1 3)
  refine ⟨seed, pi, hseed, hpi, ?_⟩
  rw [blake2s_default hc, blockBytes, digestBytes_eq, digestBytes_eq, ← hseed, ← hpi]
  simp only [List.append_assoc]

/-! ## The announced sizes and the root -/

/-- The value of the `k`-th word read (`k < 8`). -/
def rdB : ℕ → ℕ
  | 0 => 15
  | k + 1 => 31 + 15 * k

/-- The statement of the `k`-th read. -/
def rdN : ℕ → ℕ
  | 0 => 8
  | k + 1 => 22 + 14 * k

/-- The first state cell before the `k`-th read. -/
def rdS : ℕ → ℕ
  | 0 => 12
  | k + 1 => rdB k + 13

theorem vs_reads_blocks : ∀ k < 8, stmtsEqb (fsNextT (.n (rdS k)) (.n (rdS k + 1)) (.n 14) k (rdB k))
    ((vsPre.drop (rdN k)).take 13) = true := by decide +kernel

theorem vs_rows_blocks : ∀ t < 6, stmtsEqb [.atom (.load (.n (rdB (t + 1))) (.n 30) t)]
    ((vsPre.drop (rdN (t + 1) + 13)).take 1) = true := by decide +kernel

/-- The `k` first words read. -/
def readWords (σ : Val) (k : ℕ) : List E := (List.range k).map fun i ↦ σ (.n (rdB i))

theorem readWords_succ (σ : Val) (k : ℕ) :
    readWords σ (k + 1) = readWords σ k ++ [σ (.n (rdB k))] := by
  simp [readWords, List.range_succ]

theorem obsAll_append_one (cv : Digest) (xs : List E) (x : E) :
    obsAll cv (xs ++ [x]) = obsCv (obsAll cv xs) x := by
  simp [obsAll, List.foldl_append]

/-- **The eight announced words**: each at the stream's offset `k`, absorbed in order; the six row
counts stored at `table_rows`. -/
theorem vs_reads (h : VsHolds rd σ) {cv0 : Digest} (h0 : (σ (.n 12), σ (.n 13)) = digestScalars cv0) :
    (∀ k < 8, LoadHolds rd (σ (.n 14)) k (σ (.n (rdB k)))) ∧
      (∀ k ≤ 8, (σ (.n (rdS k)), σ (.n (rdS k + 1))) = digestScalars (obsAll cv0 (readWords σ k))) ∧
      ∀ t < 6, LoadHolds rd (σ (.n 30)) t (σ (.n (rdB (t + 1)))) := by
  have hb := fun k hk => h.fsNext (rdN k) _ _ _ k (rdB k) (vs_reads_blocks k hk)
  refine ⟨fun k hk => (hb k hk).1, ?_, fun t ht => ?_⟩
  · intro k hk
    induction k with
    | zero => exact h0
    | succ k ih =>
      obtain ⟨-, cv, hcv, hout⟩ := hb k (by omega)
      rw [ih (by omega)] at hcv
      rw [readWords_succ, obsAll_append_one, digestScalars_injective hcv]
      exact hout
  · have := h.atom _ _ (vs_rows_blocks t ht)
    exact this

/-- **The stack's root** (G:2129-2135): the two words at offsets `8`, `9`, absorbed, both
canonical; the root's digest. -/
theorem vs_root (h : VsHolds rd σ) {cv : Digest} (h0 : (σ (.n 134), σ (.n 135)) = digestScalars cv) :
    LoadHolds rd (σ (.n 14)) 8 (σ (.n 419)) ∧ LoadHolds rd (σ (.n 14)) 9 (σ (.n 434)) ∧
      (σ (.n 447), σ (.n 448)) = digestScalars (obsAll cv [σ (.n 419), σ (.n 434)]) ∧
      ∃ root : Digest, (σ (.n 419), σ (.n 434)) = digestScalars root := by
  obtain ⟨l8, cv8, h8, o8⟩ := h.fsNext 508 (.n 134) (.n 135) (.n 14) 8 419 (by decide +kernel)
  obtain ⟨l9, cv9, h9, o9⟩ := h.fsNext 521 (.n 432) (.n 433) (.n 14) 9 434 (by decide +kernel)
  rw [h0] at h8
  rw [← digestScalars_injective h8] at o8
  rw [o8] at h9
  rw [← digestScalars_injective h9] at o9
  have c1 := (assert_canonical_iff rd _ _).mp (h.call 534 "assert_canonical" [.n 419] [.n 449]
    (by decide +kernel))
  have c2 := (assert_canonical_iff rd _ _).mp (h.call 535 "assert_canonical" [.n 434] [.n 450]
    (by decide +kernel))
  exact ⟨l8, l9, o9, exists_digest c1.1 c2.1⟩

/-! ## The rate and the memory's log -/

/-- A range check against `g^(K-1)` on a memory of `2^κ ≥ 64` words, `K ≤ 64`: `x = g^e`,
`e < K`. -/
theorem rc_gen {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ) {x y t1 t2 k : E} {K : ℕ}
    (hK : 1 ≤ K) (hK' : K ≤ 64) (hk : k = gen ^ (K - 1)) (h1 : LoadHolds Lm.read x 0 t1)
    (h2 : k = x * y) (h3 : LoadHolds Lm.read y 0 t2) : ∃ e < K, x = gen ^ e := by
  have h64 : K ≤ 2 ^ κ := le_trans hK' (le_trans (by decide) (Nat.pow_le_pow_right (by decide) hκ6))
  obtain ⟨e, he, hx⟩ := (rangeCheck_iff hκ Lm x hK h64).mp
    ⟨y, t1, t2, h1, by rw [← h2, hk, gen_pow_eq_ofK], h3⟩
  exact ⟨e, he, by rw [hx, gen_pow_eq_ofK]⟩

theorem eq_eOfNat_of_isInK {x : E} (h : IsInK x) : x = eOfNat (kToNat (x.limb 0)) := by
  rw [eOfNat, ofBits_kToNat, ← eq_ofK_limb h]

/-- `g_power_of_word(value, g_squares, 6)` over the exponent tables: `value = E(N)`, `N < 64`, and
the result is `g^N`. -/
theorem gpw6_pow {rd : Reader} {lp sq v r : E} (ht : ExpTables rd lp sq)
    (h : coreProgram.Rel rd "g_power_of_word__L6" [v, sq] [r]) :
    ∃ N < 64, v = eOfNat N ∧ r = gen ^ N := by
  obtain ⟨hk, hlt, -, s, hs, hr, rfl⟩ := (g_power_of_word_L6_iff rd _ _).mp h
  exact ⟨_, hlt, eq_eOfNat_of_isInK hk, gpw_pow ht (by decide) hs hr hlt⟩

/-- **The rate** (G:2108-2110): the last announced word is `E(r)`, `1 ≤ r ≤ 4`, and
`rate_sel = g^(r - 1)`. -/
theorem vs_rate {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ) (h : VsHolds Lm.read σ)
    (ht : ExpTables Lm.read (σ (.n 4)) (σ (.n 5))) :
    ∃ r, 1 ≤ r ∧ r ≤ 4 ∧ σ (.n 121) = eOfNat r ∧ σ (.n 138) = gen ^ (r - 1) := by
  obtain ⟨N, hN, hv, hr⟩ := gpw6_pow ht (h.call 119 "g_power_of_word__L6" [.n 121, .n 5] [.n 136]
    (by decide +kernel))
  have hs := h.slice 120 [.atom (.const (.n 137) (word 2 0 0)),
    .atom (.mul (.n 136) (.n 138) (.n 137)), .atom (.const (.n 139) (word 8 0 0)),
    .atom (.rangeCheck (.n 138) (.n 140) (.n 141) (.n 142) (.n 139))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hs
  obtain ⟨h137, h136, h139, ⟨r1, r2, r3⟩⟩ := hs
  obtain ⟨e, he, hx⟩ := rc_gen hκ hκ6 Lm (K := 4) (by decide) (by decide)
    (by rw [h139]; exact word_two_pow (a := 3) (by decide)) r1 r2 r3
  rw [h137, word_gen, hx, gen_pow_mul_gen] at h136
  rw [h136] at hr
  have := gen_pow_inj (by omega) (by omega) hr
  exact ⟨N, by omega, by omega, hv, by rw [hx, show N - 1 = e by omega]⟩

/-- **The memory's log** (G:2111-2114): the first announced word is `E(m)`, `16 ≤ m ≤ 32`, and
`dims_g[0] = g^m`. -/
theorem vs_logMem {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ) {N : ℕ} (h : VsHoldsTo N Lm.read σ) (hN : 132 ≤ N)
    (ht : ExpTables Lm.read (σ (.n 4)) (σ (.n 5))) :
    ∃ m, 16 ≤ m ∧ m ≤ 32 ∧ σ (.n 15) = eOfNat m ∧ σ (.n 144) = gen ^ m := by
  replace h := h.mono hN
  obtain ⟨N, hN, hv, hr⟩ := gpw6_pow ht (h.call' 125 "g_power_of_word__L6" [.n 15, .n 5] [.n 144]
    (by decide +kernel))
  have hs := h.slice' 126 [.atom (.const (.n 145) (word 4294967296 0 0)),
    .atom (.rangeCheck (.n 144) (.n 146) (.n 147) (.n 148) (.n 145)),
    .atom (.const (.n 149) (word 4294967296 0 0)), .atom (.const (.n 150) (word 65536 0 0)),
    .atom (.mul (.n 144) (.n 151) (.n 150)),
    .atom (.rangeCheck (.n 151) (.n 152) (.n 153) (.n 154) (.n 149))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hs
  obtain ⟨h145, ⟨r1, r2, r3⟩, h149, h150, h144, ⟨s1, s2, s3⟩⟩ := hs
  obtain ⟨e, he, hx⟩ := rc_gen hκ hκ6 Lm (K := 33) (by decide) (by decide)
    (by rw [h145]; exact word_two_pow (a := 32) (by decide)) r1 r2 r3
  obtain ⟨e', he', hx'⟩ := rc_gen hκ hκ6 Lm (K := 33) (by decide) (by decide)
    (by rw [h149]; exact word_two_pow (a := 32) (by decide)) s1 s2 s3
  have w16 : word 65536 0 0 = gen ^ 16 := word_two_pow (a := 16) (by decide)
  rw [h150, w16, hx', ← pow_add] at h144
  rw [hr] at hx h144
  have h1 := gen_pow_inj (by omega) (by omega) hx
  have h2 := gen_pow_inj (by omega) (by omega) h144
  exact ⟨N, by omega, by omega, hv, hr⟩

/-! ## The kappas -/

/-- `kappa_base`'s hinted words: `dims_g[1..7]`. -/
def dimsWords (σ : Val) : List E := (List.range 6).map fun t ↦ σ (.n (157 + t))

/-- The value block `b` of `block_kappa` loads. -/
def bkV (b : ℕ) : ℕ := 164 + b + (if 2 < b then 2 else 0) + (if 39 < b then 2 else 0)

/-- Block `b`'s first statement. -/
def bkStmt (b : ℕ) : ℕ := 151 + 2 * b + (if 2 < b then 2 else 0) + (if 39 < b then 2 else 0)

theorem vs_kb_blocks : ∀ b < 102, b ≠ 2 → b ≠ 39 →
    (decide (bkStmt b + 2 ≤ 359) && stmtsEqb [.atom (.load (.n (bkV b)) (.n 155) (blockKappaSrc.getD b 0)),
      .atom (.load (.n (bkV b)) (.n 163) b)] ((vsPre.drop (bkStmt b)).take 2)) = true := by
  decide +kernel

theorem vs_kb_adj : ∀ b ∈ [2, 39],
    (decide (bkStmt b + 4 ≤ 359) && stmtsEqb [.atom (.load (.n (bkV b)) (.n 155) 0),
      .atom (.const (.n (bkV b + 1)) (word 262144 0 0)),
      .atom (.mul (.n (bkV b + 2)) (.n (bkV b)) (.n (bkV b + 1))),
      .atom (.load (.n (bkV b + 2)) (.n 163) b)] ((vsPre.drop (bkStmt b)).take 4)) = true := by
  decide +kernel

theorem vs_kbase_blocks : ∀ t < 6,
    (decide (138 + 2 * t + 2 ≤ 359) && stmtsEqb [.atom (.load (.n (157 + t)) (.n 143) (1 + t)),
      .atom (.load (.n (157 + t)) (.n 155) (2 + t))] ((vsPre.drop (138 + 2 * t)).take 2)) = true := by
  decide +kernel

theorem blockKappaSrc_lt : ∀ b < 102, blockKappaSrc.getD b 0 < 8 := by decide

theorem blockKappaAdj_eq : ∀ b < 102, blockKappaAdj.getD b 0 = if b = 2 ∨ b = 39 then 18 else 0 := by
  decide

/-- **`dims_g` and `block_kappa`** (G:2113-2123): `dims_g` holds `g^log_mem` then the hinted
words, and `block_kappa` the blocks' kappas over them. -/
theorem vs_kappas {N : ℕ} (h : VsHoldsTo N rd σ) (hN : 359 ≤ N) :
    ReadsAt rd (σ (.n 143)) (σ (.n 144) :: dimsWords σ) ∧
      ReadsAt rd (σ (.n 155)) (kappaBase (σ (.n 144)) (dimsWords σ)) ∧
      ReadsAt rd (σ (.n 163)) (blockKappas (σ (.n 144)) (dimsWords σ)) := by
  replace h := h.mono hN
  have h132 := h.atom' 132 (.load (.n 144) (.n 143) 0) (by decide +kernel)
  have hb3 := h.slice' 135 [.atom (.const (.n 156) (word 1 0 0)), .atom (.load (.n 156) (.n 155) 0),
    .atom (.load (.n 144) (.n 155) 1)] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one] at hb3
  obtain ⟨h156, l0, l1⟩ := hb3
  rw [h156] at l0
  have hk := fun t (ht : t < 6) => by
    have := h.slice' _ _ (vs_kbase_blocks t ht)
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
    exact this
  have hdims : ReadsAt rd (σ (.n 143)) (σ (.n 144) :: dimsWords σ) := by
    intro k hk'
    cases k with
    | zero => exact h132
    | succ t =>
      simp only [dimsWords, List.length_cons, List.length_map, List.length_range] at hk'
      simpa [dimsWords, Nat.add_comm 1 t] using (hk t (by omega)).1
  have hbase : ReadsAt rd (σ (.n 155)) (kappaBase (σ (.n 144)) (dimsWords σ)) := by
    intro k hk'
    simp only [kappaBase, dimsWords, List.length_cons, List.length_map, List.length_range] at hk'
    match k, hk' with
    | 0, _ => simpa [kappaBase] using l0
    | 1, _ => simpa [kappaBase] using l1
    | t + 2, _ => simpa [kappaBase, dimsWords, Nat.add_comm 2 t] using (hk t (by omega)).2
  have hbase' : ∀ j < 8, LoadHolds rd (σ (.n 155)) j ((kappaBase (σ (.n 144)) (dimsWords σ)).getD j 0) :=
    fun j hj => by
      have hl : j < (kappaBase (σ (.n 144)) (dimsWords σ)).length := by
        simp [kappaBase, dimsWords]; omega
      rw [List.getD_eq_getElem _ _ hl]
      exact hbase j hl
  have hblk : ∀ b < 102, LoadHolds rd (σ (.n 163)) b
      ((kappaBase (σ (.n 144)) (dimsWords σ)).getD (blockKappaSrc.getD b 0) 0 *
        gen ^ blockKappaAdj.getD b 0) := fun b hb => by
    rw [blockKappaAdj_eq b hb]
    by_cases hadj : b = 2 ∨ b = 39
    · have hs := h.slice' _ _ (vs_kb_adj b (by rcases hadj with rfl | rfl <;> simp))
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hs
      obtain ⟨la, hc, hm, lb⟩ := hs
      have hsrc0 : blockKappaSrc.getD b 0 = 0 := by rcases hadj with rfl | rfl <;> rfl
      have w18 : word 262144 0 0 = gen ^ 18 := word_two_pow (a := 18) (by decide)
      rw [hm, hc, loadHolds_unique la (hbase' 0 (by decide)), w18] at lb
      rw [hsrc0]
      simp only [hadj, ↓reduceIte]
      exact lb
    · have hs := h.slice' _ _ (vs_kb_blocks b hb (fun e => hadj (Or.inl e))
        (fun e => hadj (Or.inr e)))
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hs
      obtain ⟨la, lb⟩ := hs
      rw [← loadHolds_unique la (hbase' _ (blockKappaSrc_lt b hb))]
      simp only [hadj, ↓reduceIte, pow_zero, mul_one]
      exact lb
  refine ⟨hdims, hbase, fun b hb => ?_⟩
  simp only [blockKappas, List.length_map, List.length_range] at hb
  simpa [blockKappas] using hblk b hb

/-! ## The push side's total and the bus depth -/

/-- The value of the `b`-th push block's kappa, as the product loads it. -/
def pushK (b : ℕ) : ℕ := if b = 0 then 270 else 273 + 4 * (b - 1)

/-- The running product after block `b`. -/
def pushP (b : ℕ) : ℕ := if b = 0 then 272 else pushK b + 3

/-- Block `b`'s first statement. -/
def pushStmt (b : ℕ) : ℕ := if b = 0 then 359 else 362 + 4 * (b - 1)

theorem vs_push_blocks : ∀ b < 36,
    stmtsEqb [.atom (.load (.n (pushK (b + 1))) (.n 163) (b + 1)),
      .atom (.mul (.n (pushK (b + 1) + 1)) (.n 5) (.n (pushK (b + 1)))),
      .atom (.load (.n (pushK (b + 1) + 2)) (.n (pushK (b + 1) + 1)) 0),
      .atom (.mul (.n (pushP (b + 1))) (.n (pushP b)) (.n (pushK (b + 1) + 2)))]
      ((vsPre.drop (pushStmt (b + 1))).take 4) = true := by decide +kernel

/-- **The push side's total** (G:2124-2128): `push_total` is the product of the words
`g_squares[block_kappa[g^b]]`, `b < 37`. -/
theorem vs_push (h : VsHolds rd σ) :
    (∀ b < 37, LoadHolds rd (σ (.n 163)) b (σ (.n (pushK b))) ∧
      LoadHolds rd (σ (.n 5) * σ (.n (pushK b))) 0 (σ (.n (pushK b + 2)))) ∧
      σ (.n 416) = ((List.range 37).map fun b ↦ σ (.n (pushK b + 2))).prod := by
  have h0 := h.slice 359 [.atom (.load (.n 270) (.n 163) 0), .atom (.mul (.n 271) (.n 5) (.n 270)),
    .atom (.load (.n 272) (.n 271) 0)] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h0
  obtain ⟨a0, m0, b0⟩ := h0
  have hs := fun b (hb : b < 36) => by
    have := h.slice _ _ (vs_push_blocks b hb)
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
    exact this
  refine ⟨fun b hb => ?_, ?_⟩
  · cases b with
    | zero =>
      refine ⟨a0, ?_⟩
      show LoadHolds rd (σ (.n 5) * σ (.n 270)) 0 (σ (.n 272))
      rw [← m0]; exact b0
    | succ b =>
      obtain ⟨a, m, l, -⟩ := hs b (by omega)
      exact ⟨a, by rw [← m]; exact l⟩
  · have hp : ∀ b < 37, σ (.n (pushP b)) = ((List.range (b + 1)).map fun b ↦ σ (.n (pushK b + 2))).prod := by
      intro b hb
      induction b with
      | zero => simp [pushP, pushK]
      | succ b ih =>
        obtain ⟨-, -, -, hm⟩ := hs b (by omega)
        rw [hm, ih (by omega), List.range_succ (n := b + 1), List.map_append, List.prod_append]
        simp
    simpa [pushP, pushK] using hp 36 (by omega)

/-- **The bus depth** (G:2128): `g_bus_mu = g^(log2Ceil N)` for the push total `g^N`, `N < 2^34`,
the log below 34. -/
theorem vs_busMu {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ) (h : VsHolds Lm.read σ)
    (ht : ExpTables Lm.read (σ (.n 4)) (σ (.n 5))) :
    ∃ N < 2 ^ 34, σ (.n 416) = gen ^ N ∧ log2Ceil N < 34 ∧ σ (.n 417) = gen ^ log2Ceil N := by
  have hc := h.call 506 "log2_ceil_in_the_exponent__L0_L34" [.n 416, .n 4, .n 5] [.n 417]
    (by decide +kernel)
  obtain ⟨N, hN, hg, hl, -, -, hr⟩ :=
    (log2_ceil_in_the_exponent_L0_L34_iff hκ hκ6 Lm ht _).mp hc
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, Nat.zero_max] at hr hl
  exact ⟨N, hN, hg, hl, hr⟩

end
end LeanVM.Guest.B1.VerifySub
