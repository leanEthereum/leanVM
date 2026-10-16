module

public import LeanVMCircuits.Rec.GkrInst

@[expose] public section

/-!
The zerocheck of flock's reduction over the `HASH` rows: its honest instance after the univariate skip, the skip's
interpolation, and the two draw events its soundness needs.

The witness (`Tables`): the zerocheck's three tables `a = A z`, `b = B z`, `c = z` on the bit positions of the packed
`HASH` region, each value a bit (`ZMod 2`), `z` the committed bits and `A`, `B` the circuit's fixed matrices
(`Tables.ofWitness`, `blockMatrix`: `A = I_rows ⊗ A0`). Position `u = i + 64 v` is bit `i` of word `v`: the low six
coordinates are the skip's, the `n` others the multilinear rounds'. Row `u` holds when `a(u) b(u) + c(u) = 0`
(`Viol`: some row of the `2^(n + 6)` does not).

The skip domain `S` (`sNode`, `PHI8_TABLE[0..64]`) and its coset `Λ` (`lNode`, `PHI8_TABLE[64..128]`), as the
recursion circuit's constants name them. `V_S(X) = X^64 + Σ_j c_j X^(2^j)` (`vanS`, `SkipDomain::vanishing`'s
coefficients) vanishes on `S` and is the constant `V_S(λ_0)` (`offWord`) on `Λ`, so `V_Λ = V_S + V_S(λ_0)` (`vanL`)
vanishes on `Λ` (`sWords_van`, `lWords_van`, `skipOk`: kernel-checked on the words, eight nodes per check). In
characteristic two `V_S' = c_0`, so the quotient `V_S / (X - s_i)` is `c_0` at `s_i` and zero on the rest of `S`:
`lagS i = D_64 · V_S / (X - s_i)` is `S`'s Lagrange basis (`lagS_node`), `D_64 c_0 = 1`, and `lagS_eval`: where
`(ζ + s_i) h = 1`, `D_64 V_S(ζ) h = L_i(ζ)`, the form `SkipDomain::lagrange_at` computes. Likewise
`phat v = D_128 V_S · Σ_i v_i V_Λ / (X - λ_i)` is zero on `S` and `v` on `Λ` (`phat_sNode`, `phat_lNode`), of degree
at most `127` (`phat_natDegree`), the only such polynomial (`phat_unique`), and `phat_eval`: where every
`(ζ + λ_i) h_i = 1`, `D_128 V_S(ζ) V_Λ(ζ) Σ_i v_i h_i`, what `SkipDomain::first_round_at` computes, is `phat v` at `ζ`.

The quirky extension of a table `t` (`quirky`): `t*(Y, X) = Σ_i L_i(Y) · mle(t_i)(X)`, `t_i(v) = t(i + 64 v)`.
`zeroInst n r T ζ = eqInst n r (a* b* + c*)(ζ, ·)`: the zerocheck's multilinear rounds after the skip. `zeroInst_sum`,
`zeroInst_ok` (degree `2`), `zeroInst_final` (the triple `a*, b*, c*` at `(ζ, χ)`), `zeroInst_weight` (round `i`
factors out `r_i`). As a polynomial in `ζ` the sum is `honestP n r T` (`honestP_eval`), of degree at most `126`, and
at `s_j` it is row `j`'s eq-weighted sum `rowSum` (`honestP_sNode`).

The skip's event (`skipDraws`): `phat v ≠ honestP` yet they agree at `ζ`, at most `127` of the `ζ`
(`skipDraws_card`). Off it, the zerocheck's input claim being both makes every `rowSum` zero (`rows_of_skip`).

The fixed coordinates: the zerocheck's first seven eq coordinates are constants (`fixedWords`: three small, then four
medium), the rest drawn. Their `128` eq weights (`eqWords`: each a medium weight times a small one, `eq_rows`) are
linearly independent over `GF(2)` (`fixed_indep`, a dual basis `dualWords` checked in the kernel, `dual_rows`), so a
broken row leaves its slice's weighted sum a nonzero multilinear polynomial in the drawn coordinates `ρ`, of total
degree at most `n'`: the event `fixDraws` (some row broken, yet every slice's sum zero at `r = fixed ++ ρ`) is at most
an `n'/|E|` fraction of the `ρ` (`fixDraws_card`), and off it the zero sums give every row (`no_viol_of_rows`).
-/

namespace LeanVMCircuits.Rec.Flock

open LeanVMCircuits.Rec AirLink Sumcheck Polynomial Finset

/-! The constants. -/

/-- Three limb words of an `E` element. -/
abbrev W3 := ℕ × ℕ × ℕ

/-- The `K` element of a word in `E`, as `e_const(w, 0, 0)` makes it. -/
noncomputable def kw (w : ℕ) : E := emb (ofWord w)

/-- The `E` element of three limb words, as `e_const` makes it. -/
noncomputable def ew (w : W3) : E := toE (ofWord w.1) (ofWord w.2.1) (ofWord w.2.2)

/-- The skip domain `S`: `PHI8_TABLE[0..64]`, the recursion circuit's nodes of `lagrange_at`. -/
def sWords : List ℕ := [
  0, 1, 233317187178767958, 233317187178767959,
  5847396588373319944, 5847396588373319945, 5916261553440163678, 5916261553440163679,
  909273441170553857, 909273441170553856, 1126616643693337175, 1126616643693337174,
  6753221685647269129, 6753221685647269128, 6810757554037128031, 6810757554037128030,
  13425015913296524956, 13425015913296524957, 13363258058013790410, 13363258058013790411,
  16963121286284040084, 16963121286284040085, 16741555821419917762, 16741555821419917763,
  13173415632012282525, 13173415632012282524, 13109335328444067019, 13109335328444067018,
  16714968798032636821, 16714968798032636820, 16486437098630516163, 16486437098630516162,
  13413663147086793287, 13413663147086793286, 13337989939188722705, 13337989939188722704,
  16933754119322725199, 16933754119322725198, 16734302103207496985, 16734302103207496984,
  13166419680609547846, 13166419680609547847, 13079698300183580688, 13079698300183580689,
  16689958445912364878, 16689958445912364879, 16474814470949679384, 16474814470949679385,
  29795976497216731, 29795976497216730, 240155289994828429, 240155289994828428,
  5859178164118920659, 5859178164118920658, 5941114056868903813, 5941114056868903812,
  934417933708345562, 934417933708345563, 1138091936817112716, 1138091936817112717,
  6760351777467556306, 6760351777467556307, 6840247247740520324, 6840247247740520325]

/-- The coset `Λ = S + phi_8(64)`: `PHI8_TABLE[64..128]`, the nodes of `first_round_at`. -/
def lWords : List ℕ := [
  5077413140227349505, 5077413140227349504, 4992927275758287447, 4992927275758287446,
  1680045447218232585, 1680045447218232584, 1471640032698489695, 1471640032698489694,
  5397840376063860736, 5397840376063860737, 5319898533665736278, 5319898533665736279,
  2003779738599850248, 2003779738599850249, 1797556034875041630, 1797556034875041631,
  18174738647891815069, 18174738647891815068, 18376177690117868747, 18376177690117868746,
  12474835414352726933, 12474835414352726932, 12547991768974339523, 12547991768974339522,
  17341048660226299548, 17341048660226299549, 17553676061639045322, 17553676061639045323,
  11637837820279650196, 11637837820279650197, 11726545947089916354, 11726545947089916355,
  18181172200248022598, 18181172200248022599, 18405252315020079120, 18405252315020079121,
  12499283362976839502, 12499283362976839503, 12559051997470757144, 12559051997470757145,
  17351837927878388295, 17351837927878388294, 17578380677594729489, 17578380677594729488,
  11666641484232641359, 11666641484232641358, 11733236166605761817, 11733236166605761816,
  5052831051185709274, 5052831051185709275, 4982014381818922636, 4982014381818922637,
  1673477754444464594, 1673477754444464595, 1442712742353364868, 1442712742353364869,
  5368607902574976219, 5368607902574976218, 5313623929546259085, 5313623929546259084,
  1992561661411900883, 1992561661411900882, 1773267034315692933, 1773267034315692932]

/-- `SkipDomain::vanishing_coefficients`: `V_S(X) = X^64 + Σ_{j < 6} c_j X^(2^j)`. -/
def vanWords : List ℕ := [240155289994828428, 18174738647891815069, 1858076378458151938, 11666641484232641359,
  934417933708345563, 5456714987496728454]

/-- `V_S(λ_0)`, the constant `first_round_at` adds to `V_S` for `V_Λ`. -/
def offWord : ℕ := 16933754119322725199

/-- `D_128 = 1 / Π_{k ≠ 0} phi_8(k)` over the window `S ∪ Λ` (`window_denominator(128)`). -/
def d128Word : ℕ := 233317187178767959

/-- `D_64 = 1 / Π_{k ≠ 0, k < 64} phi_8(k)` over `S` (`window_denominator(64)`). -/
def d64Word : ℕ := 11666641484232641359

/-- The three small fixed eq coordinates (`small_challenges`), as the circuit's `e_const`s. -/
def smallWords : List W3 := [(5772811086190238293, 0, 0), (18376177690117868746, 0, 0), (1537792354547671042, 0, 0)]

/-- The four medium fixed eq coordinates (`medium_challenges`), as the circuit's `e_const`s. -/
def medWords : List W3 := [(3877548338577296374, 1367482035892397521, 13373126565067795492),
  (7200243516802924451, 16251485319816311889, 13522021764491415548),
  (14498505783250251438, 16564499533431716054, 16770611540025040673),
  (3934799921294095118, 853327055063395975, 1309330797735322834)]

/-- The seven fixed eq coordinates: the small ones, then the medium ones. -/
def fixedWords : List W3 := smallWords ++ medWords

/-! The skip domain on words. -/

/-- `x, x^2, x^4, ..., x^(2^k)`, each the square of the one before. -/
def sqs : ℕ → ℕ → List ℕ
  | 0, x => [x]
  | k + 1, x => x :: sqs k (mul x x)

/-- Every squared word is below `2^64`, as `Field.mul` reads it. -/
def sqsOk : ℕ → ℕ → Bool
  | 0, _ => true
  | k + 1, x => decide (x < 2 ^ 64) && sqsOk k (mul x x)

/-- Coefficient `c_j` of `V_S`. -/
def vc (j : ℕ) : ℕ := vanWords.getD j 0

/-- `x^(2^j)` on words. -/
def pw (x j : ℕ) : ℕ := (sqs 6 x).getD j 0

/-- `V_S(x)` on words. -/
def vanW (x : ℕ) : ℕ :=
  pw x 6 ^^^ mul (pw x 0) (vc 0) ^^^ mul (pw x 1) (vc 1) ^^^ mul (pw x 2) (vc 2) ^^^ mul (pw x 3) (vc 3) ^^^
    mul (pw x 4) (vc 4) ^^^ mul (pw x 5) (vc 5)

/-- `V_S(x) = t` on words below `2^64`. -/
def vanOk (t x : ℕ) : Bool := decide (t < 2 ^ 64) && decide (x < 2 ^ 64) && sqsOk 6 x && vanW x == t

/-- Nodes `lo` to `lo + 7` of `ws` meet `V_S = t`: the kernel checks the nodes eight at a time. -/
def vanChunk (t : ℕ) (ws : List ℕ) (lo : ℕ) : Bool := (List.range 8).all fun k => vanOk t (ws.getD (lo + k) 0)

theorem sChunk0 : vanChunk 0 sWords 0 = true := by decide +kernel
theorem sChunk1 : vanChunk 0 sWords 8 = true := by decide +kernel
theorem sChunk2 : vanChunk 0 sWords 16 = true := by decide +kernel
theorem sChunk3 : vanChunk 0 sWords 24 = true := by decide +kernel
theorem sChunk4 : vanChunk 0 sWords 32 = true := by decide +kernel
theorem sChunk5 : vanChunk 0 sWords 40 = true := by decide +kernel
theorem sChunk6 : vanChunk 0 sWords 48 = true := by decide +kernel
theorem sChunk7 : vanChunk 0 sWords 56 = true := by decide +kernel
theorem lChunk0 : vanChunk offWord lWords 0 = true := by decide +kernel
theorem lChunk1 : vanChunk offWord lWords 8 = true := by decide +kernel
theorem lChunk2 : vanChunk offWord lWords 16 = true := by decide +kernel
theorem lChunk3 : vanChunk offWord lWords 24 = true := by decide +kernel
theorem lChunk4 : vanChunk offWord lWords 32 = true := by decide +kernel
theorem lChunk5 : vanChunk offWord lWords 40 = true := by decide +kernel
theorem lChunk6 : vanChunk offWord lWords 48 = true := by decide +kernel
theorem lChunk7 : vanChunk offWord lWords 56 = true := by decide +kernel

theorem chunks_all {t : ℕ} {ws : List ℕ} (h : ∀ k < 8, vanChunk t ws (8 * k) = true) :
    ∀ i < 64, vanOk t (ws.getD i 0) = true := by
  intro i hi
  have := h (i / 8) (by omega)
  simp only [vanChunk, List.all_eq_true, List.mem_range] at this
  have := this (i % 8) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at this

/-- `V_S` vanishes on `S`. -/
theorem sWords_van : ∀ i < 64, vanOk 0 (sWords.getD i 0) = true := chunks_all fun k hk => by
  interval_cases k
  exacts [sChunk0, sChunk1, sChunk2, sChunk3, sChunk4, sChunk5, sChunk6, sChunk7]

/-- `V_S` is `V_S(λ_0)` on `Λ`. -/
theorem lWords_van : ∀ i < 64, vanOk offWord (lWords.getD i 0) = true := chunks_all fun k hk => by
  interval_cases k
  exacts [lChunk0, lChunk1, lChunk2, lChunk3, lChunk4, lChunk5, lChunk6, lChunk7]

/-- The skip domain's other facts on words: the `128` nodes are distinct, and `D_128 V_S(λ_0) c_0 = 1`,
`D_64 c_0 = 1`. -/
def skipOk : Bool :=
  sWords.length == 64 && lWords.length == 64 && vanWords.length == 6 && vanWords.all (· < 2 ^ 64) &&
    decide (sWords ++ lWords).Nodup && decide (d128Word < 2 ^ 64) && decide (d64Word < 2 ^ 64) &&
    mul (mul d128Word offWord) (vc 0) == 1 && mul d64Word (vc 0) == 1

theorem skipOk_eq : skipOk = true := by decide +kernel

/-! Words as field elements. -/

theorem ofWord_lt {w : ℕ} (h : w < 2 ^ 64) : ofWord w = ev w := by rw [ofWord, Nat.mod_eq_of_lt h]

theorem kw_lt {w : ℕ} (h : w < 2 ^ 64) : kw w = emb (ev w) := by rw [kw, ofWord_lt h]

theorem kw_inj {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : kw a = kw b) : a = b := by
  rw [← toWord_ofWord a ha, ← toWord_ofWord b hb, emb_injective h]

theorem negE (a : E) : -a = a := by
  have h : a + a = 0 := by rw [← two_mul, two_E, zero_mul]
  linear_combination -h

theorem sub_eq_addE (a b : E) : a - b = a + b := by rw [sub_eq_add_neg, negE]

theorem ev_sqs : ∀ (k x : ℕ), sqsOk k x = true → ∀ j ≤ k, ev ((sqs k x).getD j 0) = ev x ^ 2 ^ j
  | 0, x, _, j, hj => by
    obtain rfl : j = 0 := by omega
    simp [sqs]
  | k + 1, x, h, j, hj => by
    simp only [sqsOk, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases j with _ | j
    · simp [sqs]
    · simp only [sqs, List.getD_cons_succ]
      rw [ev_sqs k _ h.2 j (by omega), ev_mul _ _ h.1, ← sq, ← pow_mul, ← pow_succ']

theorem all_getD {l : List ℕ} {p : ℕ → Bool} (h : l.all p = true) {i : ℕ} (hi : i < l.length) :
    p (l.getD i 0) = true := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.all_eq_true.mp h _ (List.getElem_mem hi)

theorem skip_facts :
    sWords.length = 64 ∧ lWords.length = 64 ∧ vanWords.length = 6 ∧ (∀ j < 6, vc j < 2 ^ 64) ∧
      (∀ i < 64, vanOk 0 (sWords.getD i 0) = true) ∧ (∀ i < 64, vanOk offWord (lWords.getD i 0) = true) ∧
      (sWords ++ lWords).Nodup ∧ d128Word < 2 ^ 64 ∧ d64Word < 2 ^ 64 ∧
      mul (mul d128Word offWord) (vc 0) = 1 ∧ mul d64Word (vc 0) = 1 := by
  have h := skipOk_eq
  simp only [skipOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hs, hl⟩, hv⟩, hva⟩, hnd⟩, hd1⟩, hd2⟩, hm1⟩, hm2⟩ := h
  refine ⟨hs, hl, hv, fun j hj => ?_, sWords_van, lWords_van, hnd, hd1, hd2, hm1, hm2⟩
  simpa [vc] using all_getD hva (by omega : j < vanWords.length)

theorem emb_pow (a : K) (n : ℕ) : emb (a ^ n) = emb a ^ n := map_pow _ a n

theorem emb_one' : emb 1 = 1 := map_one _

/-! The vanishing polynomials. -/

/-- `V_S(X) = X^64 + Σ_j c_j X^(2^j)`, vanishing on `S`. -/
noncomputable def vanS : E[X] := X ^ 64 + ∑ j ∈ range 6, C (kw (vc j)) * X ^ 2 ^ j

/-- `V_Λ = V_S + V_S(λ_0)`, vanishing on `Λ`. -/
noncomputable def vanL : E[X] := vanS + C (kw offWord)

theorem vanS_eval (ζ : E) : vanS.eval ζ = ζ ^ 64 + ∑ j ∈ range 6, kw (vc j) * ζ ^ 2 ^ j := by
  simp [vanS, Polynomial.eval_finsetSum]

theorem vanS_kw {t x : ℕ} (h : vanOk t x = true) : vanS.eval (kw x) = kw t := by
  simp only [vanOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨ht, hx⟩, hs⟩, hv⟩ := h
  obtain ⟨-, -, -, hc, -⟩ := skip_facts
  have hp : ∀ j ≤ 6, ev (pw x j) = ev x ^ 2 ^ j := ev_sqs 6 x hs
  rw [vanS_eval, kw_lt ht, ← hv, kw_lt hx]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [kw_lt (hc 0 (by norm_num)), kw_lt (hc 1 (by norm_num)), kw_lt (hc 2 (by norm_num)), kw_lt (hc 3 (by norm_num)),
    kw_lt (hc 4 (by norm_num)), kw_lt (hc 5 (by norm_num)), vanW]
  simp only [ev_xor, ev_mul _ _ (hc 0 (by norm_num)), ev_mul _ _ (hc 1 (by norm_num)),
    ev_mul _ _ (hc 2 (by norm_num)), ev_mul _ _ (hc 3 (by norm_num)), ev_mul _ _ (hc 4 (by norm_num)),
    ev_mul _ _ (hc 5 (by norm_num)), hp 0 (by norm_num), hp 1 (by norm_num), hp 2 (by norm_num),
    hp 3 (by norm_num), hp 4 (by norm_num), hp 5 (by norm_num), hp 6 (by norm_num), emb_add, emb_mul, emb_pow]
  ring

/-- The window's nodes: `S`, then `Λ`. -/
noncomputable def node (i : ℕ) : E := kw ((sWords ++ lWords).getD i 0)

/-- Node `i` of `S`. -/
noncomputable def sNode (i : Fin 64) : E := kw (sWords.getD i 0)

/-- Node `i` of `Λ`. -/
noncomputable def lNode (i : Fin 64) : E := kw (lWords.getD i 0)

theorem sNode_eq (i : Fin 64) : sNode i = node i := by
  obtain ⟨hs, -⟩ := skip_facts
  rw [sNode, node, List.getD_append _ _ _ _ (by omega)]

theorem lNode_eq (i : Fin 64) : lNode i = node (64 + i) := by
  obtain ⟨hs, -⟩ := skip_facts
  rw [lNode, node, List.getD_append_right _ _ _ _ (by omega), hs, Nat.add_sub_cancel_left]

theorem node_lt {i : ℕ} (hi : i < 128) : (sWords ++ lWords).getD i 0 < 2 ^ 64 := by
  obtain ⟨hs, hl, -, -, hsa, hla, -⟩ := skip_facts
  by_cases h : i < 64
  · rw [List.getD_append _ _ _ _ (by omega)]
    have := hsa i h
    simp only [vanOk, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1.2
  · rw [List.getD_append_right _ _ _ _ (by omega), hs]
    have := hla (i - 64) (by omega)
    simp only [vanOk, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1.2

theorem node_inj {i j : ℕ} (hi : i < 128) (hj : j < 128) (h : node i = node j) : i = j := by
  obtain ⟨hs, hl, -, -, -, -, hnd, -⟩ := skip_facts
  have hlen : (sWords ++ lWords).length = 128 := by rw [List.length_append, hs, hl]
  have hw := kw_inj (node_lt hi) (node_lt hj) h
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at hw
  exact (hnd.getElem_inj_iff).mp hw

theorem sNode_injective : Function.Injective sNode := fun i j h => by
  rw [sNode_eq, sNode_eq] at h
  exact Fin.ext (node_inj (by omega) (by omega) h)

theorem lNode_injective : Function.Injective lNode := fun i j h => by
  rw [lNode_eq, lNode_eq] at h
  exact Fin.ext (by have := node_inj (by omega) (by omega) h; omega)

theorem vanS_sNode (i : Fin 64) : vanS.eval (sNode i) = 0 := by
  obtain ⟨-, -, -, -, hsa, -⟩ := skip_facts
  rw [sNode, vanS_kw (hsa i i.isLt), kw, ofWord_zero, emb_zero]

theorem vanS_lNode (i : Fin 64) : vanS.eval (lNode i) = kw offWord := by
  obtain ⟨-, -, -, -, -, hla, -⟩ := skip_facts
  rw [lNode, vanS_kw (hla i i.isLt)]

theorem vanL_lNode (i : Fin 64) : vanL.eval (lNode i) = 0 := by
  rw [vanL, Polynomial.eval_add, Polynomial.eval_C, vanS_lNode, ← two_mul, two_E, zero_mul]

theorem vanL_eval (ζ : E) : vanL.eval ζ = vanS.eval ζ + kw offWord := by
  rw [vanL, Polynomial.eval_add, Polynomial.eval_C]

theorem offWord_lt : offWord < 2 ^ 64 := by
  obtain ⟨-, -, -, -, -, hla, -⟩ := skip_facts
  have := hla 0 (by norm_num)
  simp only [vanOk, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1.1.1

/-- The constants' products: `D_128 V_S(λ_0) c_0 = 1` and `D_64 c_0 = 1`. -/
theorem d128_mul : kw d128Word * kw offWord * kw (vc 0) = 1 := by
  obtain ⟨-, -, -, hc, -, -, -, hd1, -, hm1, -⟩ := skip_facts
  have h := congrArg (fun w => emb (ev w)) hm1
  simp only [ev_mul _ _ (hc 0 (by norm_num)), ev_mul _ _ offWord_lt, ev_one, emb_mul, emb_one'] at h
  rw [kw_lt hd1, kw_lt offWord_lt, kw_lt (hc 0 (by norm_num)), h]

theorem d64_mul : kw d64Word * kw (vc 0) = 1 := by
  obtain ⟨-, -, -, hc, -, -, -, -, hd2, -, hm2⟩ := skip_facts
  have h := congrArg (fun w => emb (ev w)) hm2
  simp only [ev_mul _ _ (hc 0 (by norm_num)), ev_one, emb_mul, emb_one'] at h
  rw [kw_lt hd2, kw_lt (hc 0 (by norm_num)), h]

theorem two_pow_succE (k : ℕ) : (2 : E) ^ (k + 1) = 0 := by rw [pow_succ, two_E, mul_zero]

/-- In characteristic two `V_S' = c_0`. -/
theorem derivative_vanS : derivative vanS = C (kw (vc 0)) := by
  have h64 : ((64 : ℕ) : E) = 0 := by
    rw [show (64 : ℕ) = 2 ^ (5 + 1) by norm_num, Nat.cast_pow, Nat.cast_ofNat, two_pow_succE]
  rw [vanS, derivative_add, derivative_X_pow, h64, map_zero, zero_mul, zero_add, derivative_sum,
    Finset.sum_range_succ']
  rw [Finset.sum_eq_zero fun j _ => by
    rw [derivative_C_mul, derivative_X_pow, Nat.cast_pow, Nat.cast_ofNat, two_pow_succE, map_zero, zero_mul,
      mul_zero]]
  simp

theorem derivative_vanL : derivative vanL = C (kw (vc 0)) := by
  rw [vanL, derivative_add, derivative_C, add_zero, derivative_vanS]

theorem vanS_natDegree : vanS.natDegree ≤ 64 := by
  refine (natDegree_add_le _ _).trans (max_le (by rw [natDegree_X_pow]) ?_)
  refine natDegree_sum_le_of_forall_le _ _ fun j hj => (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_X_pow]
  calc 2 ^ j ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by have := mem_range.mp hj; omega)
    _ = 64 := by norm_num

theorem vanL_natDegree : vanL.natDegree ≤ 64 :=
  (natDegree_add_le _ _).trans (max_le vanS_natDegree (by rw [natDegree_C]; omega))

/-! Quotients by a root. -/

theorem quo_mul {p : E[X]} {a : E} (h : p.IsRoot a) : (X - C a) * (p /ₘ (X - C a)) = p :=
  mul_divByMonic_eq_iff_isRoot.mpr h

/-- At the root the quotient is the derivative. -/
theorem quo_eval_root {p : E[X]} {a : E} (h : p.IsRoot a) : (p /ₘ (X - C a)).eval a = (derivative p).eval a := by
  conv_rhs => rw [← quo_mul h]
  simp [derivative_mul]

/-- At another root the quotient is zero. -/
theorem quo_eval_other {p : E[X]} {a b : E} (h : p.IsRoot a) (hb : p.eval b = 0) (hab : b ≠ a) :
    (p /ₘ (X - C a)).eval b = 0 := by
  have := congrArg (eval b) (quo_mul h)
  rw [Polynomial.eval_mul, hb, Polynomial.eval_sub, eval_X, eval_C] at this
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hab
  · exact h1

theorem quo_eval {p : E[X]} {a : E} (h : p.IsRoot a) (ζ : E) : p.eval ζ = (ζ + a) * (p /ₘ (X - C a)).eval ζ := by
  conv_lhs => rw [← quo_mul h]
  rw [Polynomial.eval_mul, Polynomial.eval_sub, eval_X, eval_C, sub_eq_addE]

theorem quo_natDegree {p : E[X]} (a : E) (hp : p.natDegree ≤ 64) : (p /ₘ (X - C a)).natDegree ≤ 63 := by
  rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]
  omega

/-! `S`'s Lagrange basis. -/

/-- `L_i = D_64 · V_S / (X - s_i)`. -/
noncomputable def lagS (i : Fin 64) : E[X] := C (kw d64Word) * (vanS /ₘ (X - C (sNode i)))

theorem lagS_natDegree (i : Fin 64) : (lagS i).natDegree ≤ 63 :=
  (natDegree_C_mul_le _ _).trans (quo_natDegree _ vanS_natDegree)

/-- `L_i` is `1` at `s_i` and `0` at the rest of `S`. -/
theorem lagS_node (i j : Fin 64) : (lagS i).eval (sNode j) = if i = j then 1 else 0 := by
  rw [lagS, Polynomial.eval_mul, eval_C]
  split_ifs with hij
  · subst hij
    rw [quo_eval_root (vanS_sNode i), derivative_vanS, eval_C, mul_comm, ← d64_mul, mul_comm]
  · rw [quo_eval_other (vanS_sNode i) (vanS_sNode j) fun h => hij (sNode_injective h).symm, mul_zero]

/-- `SkipDomain::lagrange_at`'s weight: where `(ζ + s_i) h = 1`, `D_64 V_S(ζ) h = L_i(ζ)`. -/
theorem lagS_eval (i : Fin 64) {ζ h : E} (hh : (ζ + sNode i) * h = 1) :
    kw d64Word * vanS.eval ζ * h = (lagS i).eval ζ := by
  rw [lagS, Polynomial.eval_mul, eval_C, quo_eval (vanS_sNode i) ζ]
  linear_combination kw d64Word * (vanS /ₘ (X - C (sNode i))).eval ζ * hh

/-! The skip's interpolation. -/

/-- `V_Λ / (X - λ_i)`. -/
noncomputable def qL (i : Fin 64) : E[X] := vanL /ₘ (X - C (lNode i))

/-- The round-1 message's polynomial: `v` on `Λ` and zero on `S`, `D_128 V_S · Σ_i v_i V_Λ / (X - λ_i)`. -/
noncomputable def phat (v : Fin 64 → E) : E[X] := C (kw d128Word) * vanS * ∑ i, C (v i) * qL i

theorem phat_natDegree (v : Fin 64 → E) : (phat v).natDegree ≤ 127 := by
  refine (natDegree_mul_le).trans ?_
  have h1 : (C (kw d128Word) * vanS).natDegree ≤ 64 := (natDegree_C_mul_le _ _).trans vanS_natDegree
  have h2 : (∑ i, C (v i) * qL i).natDegree ≤ 63 :=
    natDegree_sum_le_of_forall_le _ _ fun i _ => (natDegree_C_mul_le _ _).trans (quo_natDegree _ vanL_natDegree)
  omega

theorem phat_sNode (v : Fin 64 → E) (j : Fin 64) : (phat v).eval (sNode j) = 0 := by
  rw [phat, Polynomial.eval_mul, Polynomial.eval_mul, vanS_sNode, mul_zero, zero_mul]

theorem phat_lNode (v : Fin 64 → E) (j : Fin 64) : (phat v).eval (lNode j) = v j := by
  rw [phat, Polynomial.eval_mul, Polynomial.eval_mul, eval_C, vanS_lNode, Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_single j (fun i _ hij => by
      rw [Polynomial.eval_mul, eval_C, qL,
        quo_eval_other (vanL_lNode i) (vanL_lNode j) fun h => hij (lNode_injective h).symm,
        mul_zero]) (by simp)]
  rw [Polynomial.eval_mul, eval_C, qL, quo_eval_root (vanL_lNode j), derivative_vanL, eval_C]
  linear_combination v j * d128_mul

/-- `SkipDomain::first_round_at`'s value: where every `(ζ + λ_i) h_i = 1`, `D_128 V_S(ζ) V_Λ(ζ) Σ_i v_i h_i` is the
round-1 message's polynomial at `ζ`. -/
theorem phat_eval (v : Fin 64 → E) {ζ : E} {h : Fin 64 → E} (hh : ∀ i, (ζ + lNode i) * h i = 1) :
    vanS.eval ζ * (vanS.eval ζ + kw offWord) * kw d128Word * ∑ i, v i * h i = (phat v).eval ζ := by
  rw [phat, Polynomial.eval_mul, Polynomial.eval_mul, eval_C, Polynomial.eval_finsetSum, mul_sum, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [Polynomial.eval_mul, eval_C, ← vanL_eval, quo_eval (vanL_lNode i) ζ, qL]
  linear_combination kw d128Word * vanS.eval ζ * v i * (vanL /ₘ (X - C (lNode i))).eval ζ * hh i

/-- A polynomial of degree at most `127` zero at the window's `128` nodes is zero. -/
theorem eq_zero_of_nodes {p : E[X]} (hp : p.natDegree ≤ 127) (h : ∀ i < 128, p.eval (node i) = 0) : p = 0 := by
  classical
  by_contra hne
  have hsub : (range 128).image node ⊆ p.roots.toFinset := fun x hx => by
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    rw [Multiset.mem_toFinset, mem_roots hne, IsRoot, h i (mem_range.mp hi)]
  have hcard : #((range 128).image node) = 128 := by
    rw [card_image_of_injOn fun i hi j hj h => node_inj (mem_range.mp hi) (mem_range.mp hj) h, card_range]
  have := (card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans (card_roots' p))
  omega

/-- The round-1 message's polynomial is the only one of degree at most `127` zero on `S` and `v` on `Λ`. -/
theorem phat_unique {v : Fin 64 → E} {P : E[X]} (hP : P.natDegree ≤ 127) (hS : ∀ j, P.eval (sNode j) = 0)
    (hL : ∀ j, P.eval (lNode j) = v j) : phat v = P := by
  refine sub_eq_zero.mp (eq_zero_of_nodes ((natDegree_sub_le _ _).trans (max_le (phat_natDegree v) hP)) fun i hi => ?_)
  rw [Polynomial.eval_sub, sub_eq_zero]
  by_cases h64 : i < 64
  · have := sNode_eq ⟨i, h64⟩
    simp only at this
    rw [← this, phat_sNode, hS]
  · have := lNode_eq ⟨i - 64, by omega⟩
    simp only [show 64 + (i - 64) = i by omega] at this
    rw [← this, phat_lNode, hL]

/-! The witness's tables and the honest instance. -/

/-- A bit in `E`. -/
noncomputable abbrev bitE : ZMod 2 →+* E := algebraMap (ZMod 2) E

/-- The zerocheck's three tables on the bit positions, each value a bit: `a = A z`, `b = B z`, `c = z`. -/
structure Tables where
  a : ℕ → ZMod 2
  b : ℕ → ZMod 2
  c : ℕ → ZMod 2

/-- The tables of the committed bits `z` and the fixed matrices `A`, `B` over the first `N` positions. -/
def Tables.ofWitness (N : ℕ) (z : ℕ → ZMod 2) (A B : ℕ → ℕ → ZMod 2) : Tables where
  a u := ∑ u' ∈ range N, A u u' * z u'
  b u := ∑ u' ∈ range N, B u u' * z u'
  c := z

/-- A block-diagonal matrix `I_rows ⊗ A0` over blocks of `2^k` positions, the form of `HASH`'s `A` and `B`. -/
def blockMatrix (k : ℕ) (A0 : ℕ → ℕ → ZMod 2) (u u' : ℕ) : ZMod 2 :=
  if u / 2 ^ k = u' / 2 ^ k then A0 (u % 2 ^ k) (u' % 2 ^ k) else 0

/-- Row `u`'s value `a(u) b(u) + c(u)`. -/
def Tables.row (T : Tables) (u : ℕ) : ZMod 2 := T.a u * T.b u + T.c u

/-- Some row of the `2^(n + 6)` breaks `a b + c = 0`. -/
def Viol (n : ℕ) (T : Tables) : Prop := ∃ u < 2 ^ (n + 6), T.row u ≠ 0

/-- Slice `i` of a table (bit `i` of every word) as a multilinear polynomial in the `n` round variables. -/
noncomputable def sliceMle (n : ℕ) (t : ℕ → ZMod 2) (i : ℕ) : MvPolynomial (Fin n) E :=
  ∑ v ∈ range (2 ^ n), eqPoly n n v * MvPolynomial.C (bitE (t (i + 64 * v)))

/-- The quirky extension at the skip challenge `ζ`: `t*(ζ, X) = Σ_i L_i(ζ) · mle(t_i)(X)`. -/
noncomputable def quirky (n : ℕ) (t : ℕ → ZMod 2) (ζ : E) : MvPolynomial (Fin n) E :=
  ∑ i : Fin 64, MvPolynomial.C ((lagS i).eval ζ) * sliceMle n t i

/-- The zerocheck's summand after the skip: `a* b* + c*` at `ζ`. -/
noncomputable def zeroPoly (n : ℕ) (T : Tables) (ζ : E) : MvPolynomial (Fin n) E :=
  quirky n T.a ζ * quirky n T.b ζ + quirky n T.c ζ

/-- The zerocheck's honest instance after the skip: `Σ_x eq(r, x) (a* b* + c*)(ζ, x)`, each round's eq weight `r_i`
factored out, binding the low variable first (`read_round(3, claim, Some(r_i))`). -/
noncomputable def zeroInst (n : ℕ) (r : Fin n → E) (T : Tables) (ζ : E) : Inst E n := eqInst n r (zeroPoly n T ζ)

theorem zeroInst_sum (n : ℕ) (r : Fin n → E) (T : Tables) (ζ : E) :
    (zeroInst n r T ζ).sum = ∑ x ∈ cube n, eqv r x * MvPolynomial.eval x (zeroPoly n T ζ) :=
  eqInst_sum r _

theorem degreeOf_sliceMle (n : ℕ) (t : ℕ → ZMod 2) (i : ℕ) (j : Fin n) :
    MvPolynomial.degreeOf j (sliceMle n t i) ≤ 1 := by
  refine (MvPolynomial.degreeOf_sum_le _ _ _).trans (Finset.sup_le fun v _ => ?_)
  exact (MvPolynomial.degreeOf_mul_C_le _ _ _).trans (degreeOf_eqPoly j)

theorem degreeOf_quirky (n : ℕ) (t : ℕ → ZMod 2) (ζ : E) (j : Fin n) :
    MvPolynomial.degreeOf j (quirky n t ζ) ≤ 1 := by
  refine (MvPolynomial.degreeOf_sum_le _ _ _).trans (Finset.sup_le fun i _ => ?_)
  exact (MvPolynomial.degreeOf_C_mul_le _ _ _).trans (degreeOf_sliceMle n t i j)

/-- The instance has degree `2`: a product of two multilinear extensions plus a third. -/
theorem zeroInst_ok (n : ℕ) (r : Fin n → E) (T : Tables) (ζ : E) : (zeroInst n r T ζ).ok 2 := by
  refine eqInst_ok 2 r _ fun j => (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
  · exact (MvPolynomial.degreeOf_mul_le _ _ _).trans
      (Nat.add_le_add (degreeOf_quirky n T.a ζ j) (degreeOf_quirky n T.b ζ j))
  · exact (degreeOf_quirky n T.c ζ j).trans (by norm_num)

/-- The instance's final value along `χ`: the triple `a*(ζ, χ) b*(ζ, χ) + c*(ζ, χ)`, the claims
`zerocheck::verify` reads. -/
theorem zeroInst_final (n : ℕ) (r : Fin n → E) (T : Tables) (ζ : E) (χ : Fin n → E) :
    (zeroInst n r T ζ).final χ = MvPolynomial.eval χ (quirky n T.a ζ) * MvPolynomial.eval χ (quirky n T.b ζ) +
      MvPolynomial.eval χ (quirky n T.c ζ) := by
  rw [zeroInst, eqInst_final, zeroPoly, map_add, map_mul]

/-- Round `i` factors out `r_i`. -/
theorem zeroInst_weight (n : ℕ) (r : Fin n → E) (T : Tables) (ζ : E) (χ : Fin n → E) (i : Fin n) :
    (zeroInst n r T ζ).weight χ i = some (r i) :=
  eqInst_weight r _ χ i

/-! The honest polynomial in the skip variable. -/

/-- A table's quirky extension at a point `x` of the round variables, as a polynomial in the skip variable. -/
noncomputable def quirkyY (n : ℕ) (t : ℕ → ZMod 2) (x : Fin n → E) : E[X] :=
  ∑ i : Fin 64, C (MvPolynomial.eval x (sliceMle n t i)) * lagS i

/-- The honest round-1 polynomial `P(Y) = Σ_x eq(r, x) (a* b* + c*)(Y, x)`. -/
noncomputable def honestP (n : ℕ) (r : Fin n → E) (T : Tables) : E[X] :=
  ∑ x ∈ cube n, C (eqv r x) * (quirkyY n T.a x * quirkyY n T.b x + quirkyY n T.c x)

theorem quirkyY_eval (n : ℕ) (t : ℕ → ZMod 2) (x : Fin n → E) (ζ : E) :
    (quirkyY n t x).eval ζ = MvPolynomial.eval x (quirky n t ζ) := by
  simp only [quirkyY, quirky, Polynomial.eval_finsetSum, Polynomial.eval_mul, eval_C, map_sum, map_mul,
    MvPolynomial.eval_C]
  exact sum_congr rfl fun i _ => mul_comm _ _

/-- At `ζ` it is the instance's sum. -/
theorem honestP_eval (n : ℕ) (r : Fin n → E) (T : Tables) (ζ : E) :
    (honestP n r T).eval ζ = (zeroInst n r T ζ).sum := by
  rw [zeroInst_sum, honestP, Polynomial.eval_finsetSum]
  refine sum_congr rfl fun x _ => ?_
  rw [Polynomial.eval_mul, eval_C, Polynomial.eval_add, Polynomial.eval_mul, quirkyY_eval, quirkyY_eval,
    quirkyY_eval, zeroPoly, map_add, map_mul]

theorem quirkyY_natDegree (n : ℕ) (t : ℕ → ZMod 2) (x : Fin n → E) : (quirkyY n t x).natDegree ≤ 63 :=
  natDegree_sum_le_of_forall_le _ _ fun i _ => (natDegree_C_mul_le _ _).trans (lagS_natDegree i)

theorem honestP_natDegree (n : ℕ) (r : Fin n → E) (T : Tables) : (honestP n r T).natDegree ≤ 126 := by
  refine natDegree_sum_le_of_forall_le _ _ fun x _ => (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_mul_le).trans ?_) ((quirkyY_natDegree n T.c x).trans ?_))
  · have := quirkyY_natDegree n T.a x
    have := quirkyY_natDegree n T.b x
    omega
  · omega

/-- Slice `j`'s rows weighted by `eq(r, ·)`: `Σ_v eq(r, v) (a b + c)(j + 64 v)`. -/
noncomputable def rowSum (n : ℕ) (r : Fin n → E) (T : Tables) (j : ℕ) : E :=
  ∑ v ∈ range (2 ^ n), eqv r (bitPoint n v) * bitE (T.row (j + 64 * v))

theorem eval_sliceMle (n : ℕ) (t : ℕ → ZMod 2) (i : ℕ) {v : ℕ} (hv : v < 2 ^ n) :
    MvPolynomial.eval (bitPoint n v) (sliceMle n t i) = bitE (t (i + 64 * v)) := by
  simp only [sliceMle, map_sum, map_mul, MvPolynomial.eval_C]
  rw [sum_congr rfl fun z hz => by rw [eval_eqPoly le_rfl (mem_range.mp hz) hv]]
  simp [hv]

/-- At `s_j` the honest polynomial is slice `j`'s weighted rows. -/
theorem honestP_sNode (n : ℕ) (r : Fin n → E) (T : Tables) (j : Fin 64) :
    (honestP n r T).eval (sNode j) = rowSum n r T j := by
  have hq : ∀ (t : ℕ → ZMod 2) (x : Fin n → E),
      (quirkyY n t x).eval (sNode j) = MvPolynomial.eval x (sliceMle n t j) := fun t x => by
    simp only [quirkyY, Polynomial.eval_finsetSum, Polynomial.eval_mul, eval_C, lagS_node, mul_ite, mul_one,
      mul_zero]
    simp
  rw [honestP, Polynomial.eval_finsetSum, sum_cube_bits, rowSum]
  refine sum_congr rfl fun v hv => ?_
  rw [Polynomial.eval_mul, eval_C, Polynomial.eval_add, Polynomial.eval_mul, hq, hq, hq,
    eval_sliceMle _ _ _ (mem_range.mp hv),
    eval_sliceMle _ _ _ (mem_range.mp hv), eval_sliceMle _ _ _ (mem_range.mp hv), Tables.row, map_add, map_mul]

/-! The skip's event. -/

open Classical in
/-- The skip's draw event for the round-1 message's polynomial `P` and the honest one `Q`: they differ, yet agree at
`ζ`. -/
noncomputable def skipDraws (P Q : E[X]) : Finset E := {ζ | P ≠ Q ∧ P.eval ζ = Q.eval ζ}

/-- The skip's event is at most `127` of the `ζ`: a nonzero difference of degree at most `127` has at most `127`
roots. -/
theorem skipDraws_card {P Q : E[X]} (hP : P.natDegree ≤ 127) (hQ : Q.natDegree ≤ 127) : #(skipDraws P Q) ≤ 127 := by
  classical
  by_cases hPQ : P = Q
  · have : skipDraws P Q = ∅ := by
      ext ζ
      simp [skipDraws, hPQ]
    rw [this, card_empty]
    omega
  · have hne : P - Q ≠ 0 := sub_ne_zero.mpr hPQ
    calc #(skipDraws P Q) ≤ (P - Q).roots.toFinset.card := by
          refine card_le_card fun ζ hζ => ?_
          simp only [skipDraws, mem_filter, mem_univ, true_and] at hζ
          rw [Multiset.mem_toFinset, mem_roots hne, IsRoot, Polynomial.eval_sub, hζ.2, sub_self]
      _ ≤ Multiset.card (P - Q).roots := Multiset.toFinset_card_le _
      _ ≤ (P - Q).natDegree := card_roots' _
      _ ≤ 127 := (natDegree_sub_le _ _).trans (max_le hP hQ)

/-- Off the skip's event, the zerocheck's input claim being both the round-1 message's polynomial at `ζ` and the
honest instance's sum makes every slice's weighted rows zero. -/
theorem rows_of_skip {n : ℕ} {r : Fin n → E} {T : Tables} {v : Fin 64 → E} {ζ : E}
    (heq : (phat v).eval ζ = (zeroInst n r T ζ).sum) (hx : ζ ∉ skipDraws (phat v) (honestP n r T)) :
    ∀ j : Fin 64, rowSum n r T j = 0 := by
  classical
  have hPQ : phat v = honestP n r T := by
    by_contra hne
    exact hx (by simp only [skipDraws, mem_filter, mem_univ, true_and]; exact ⟨hne, by rw [heq, honestP_eval]⟩)
  intro j
  rw [← honestP_sNode, ← hPQ, phat_sNode]

/-- Non-vacuity of the skip's premise: where every row holds, the honest prover's message (the honest polynomial on
`Λ`) has the honest polynomial as its interpolation, so its claim is the honest sum at every `ζ`. -/
theorem phat_honest {n : ℕ} (r : Fin n → E) {T : Tables} (h : ¬ Viol n T) :
    phat (fun i => (honestP n r T).eval (lNode i)) = honestP n r T := by
  refine phat_unique ((honestP_natDegree n r T).trans (by norm_num)) (fun j => ?_) fun j => rfl
  rw [honestP_sNode, rowSum]
  refine sum_eq_zero fun v hv => ?_
  have : T.row (j + 64 * v) = 0 := by
    by_contra hne
    exact h ⟨j + 64 * v, by have := mem_range.mp hv; have := j.isLt; rw [pow_add]; omega, hne⟩
  rw [this, map_zero, mul_zero]

/-! The fixed coordinates' eq weights. -/

/-- `E`'s product on limb words: `toE_mul`'s formula, each limb product `Field.mul`. -/
def emulW (a b : W3) : W3 :=
  (mul a.1 b.1 ^^^ (mul a.2.1 b.2.2 ^^^ mul a.2.2 b.2.1),
    mul a.1 b.2.1 ^^^ mul a.2.1 b.1 ^^^ (mul a.2.1 b.2.2 ^^^ mul a.2.2 b.2.1) ^^^ mul a.2.2 b.2.2,
    mul a.1 b.2.2 ^^^ mul a.2.1 b.2.1 ^^^ mul a.2.2 b.1 ^^^ mul a.2.2 b.2.2)

/-- The element of three limb words by `ev`. -/
noncomputable def evW (w : W3) : E := toE (ev w.1) (ev w.2.1) (ev w.2.2)

/-- Every limb below `2^64`. -/
def W3.lt (w : W3) : Bool := decide (w.1 < 2 ^ 64) && decide (w.2.1 < 2 ^ 64) && decide (w.2.2 < 2 ^ 64)

theorem W3.lt_iff (w : W3) : w.lt = true ↔ w.1 < 2 ^ 64 ∧ w.2.1 < 2 ^ 64 ∧ w.2.2 < 2 ^ 64 := by
  simp only [W3.lt, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem evW_mul (a b : W3) (hb : b.lt = true) : evW (emulW a b) = evW a * evW b := by
  obtain ⟨h0, h1, h2⟩ := (W3.lt_iff b).mp hb
  rw [evW, evW, evW, toE_mul, emulW]
  simp only [ev_xor, ev_mul _ _ h0, ev_mul _ _ h1, ev_mul _ _ h2]

theorem ew_eq_evW {w : W3} (h : w.lt = true) : ew w = evW w := by
  obtain ⟨h0, h1, h2⟩ := (W3.lt_iff w).mp h
  rw [ew, evW, ofWord_lt h0, ofWord_lt h1, ofWord_lt h2]

/-- `1 + a` on limb words. -/
def W3.onePlus (a : W3) : W3 := (a.1 ^^^ 1, a.2.1, a.2.2)

theorem evW_onePlus (a : W3) : evW a.onePlus = 1 + evW a := by
  simp only [W3.onePlus, evW, ev_xor, ev_one, toE, emb_add, emb_one']
  ring

/-- The eq weight `eq(as, u)` on limb words: bit `j` of `u` takes `as_j` or `1 + as_j`. -/
def eqW : List W3 → ℕ → W3
  | [], _ => (1, 0, 0)
  | a :: as, u => emulW (eqW as (u / 2)) (if u % 2 = 1 then a else a.onePlus)

/-- All `2^len` eq weights, sharing the products of the coordinates after the first. -/
def eqWs : List W3 → List W3
  | [] => [(1, 0, 0)]
  | a :: as => (eqWs as).flatMap fun e => [emulW e a.onePlus, emulW e a]

theorem flatMap_pairs (G : ℕ → W3) (F : ℕ → W3) (h0 h1 : W3 → W3) (hF0 : ∀ u, F (2 * u) = h0 (G u))
    (hF1 : ∀ u, F (2 * u + 1) = h1 (G u)) :
    ∀ m, ((List.range m).map G).flatMap (fun e => [h0 e, h1 e]) = (List.range (2 * m)).map F
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.flatMap_append, flatMap_pairs G F h0 h1 hF0 hF1 m,
      show 2 * (m + 1) = 2 * m + 1 + 1 by ring, List.range_succ, List.range_succ, List.map_append, List.map_append,
      List.append_assoc]
    simp [hF0, hF1]

theorem eqWs_eq : ∀ as : List W3, eqWs as = (List.range (2 ^ as.length)).map (eqW as)
  | [] => rfl
  | a :: as => by
    rw [eqWs, eqWs_eq as, List.length_cons, pow_succ, mul_comm]
    refine flatMap_pairs _ _ _ _ (fun u => ?_) (fun u => ?_) _
    · simp [eqW]
    · simp only [eqW]
      rw [show (2 * u + 1) / 2 = u by omega, if_pos (by omega)]

/-- The eq weights as field elements: bit `j` of `u` takes the coordinate or one plus it. -/
theorem evW_eqW : ∀ (as : List W3), (∀ a ∈ as, a.lt = true ∧ a.onePlus.lt = true) → ∀ u : ℕ,
    evW (eqW as u) = ∏ j ∈ range as.length, (if u.testBit j then evW (as.getD j (0, 0, 0)) else
      1 + evW (as.getD j (0, 0, 0)))
  | [], _, u => by simp [eqW, evW, ev_one, ev_zero, toE, emb_one', emb_zero]
  | a :: as, h, u => by
    rw [eqW, List.length_cons, prod_range_succ', evW_mul _ _ (by split_ifs <;> simp_all),
      evW_eqW as (fun b hb => h b (List.mem_cons_of_mem _ hb)) (u / 2)]
    congr 1
    · refine prod_congr rfl fun j _ => ?_
      simp only [List.getD_cons_succ, Nat.testBit_div_two]
    · simp only [List.getD_cons_zero, Nat.testBit_zero]
      split_ifs with h1 h2 h2
      · rfl
      · simp at h2; omega
      · simp at h2; omega
      · exact evW_onePlus a

/-! `GF(2)`-linear functionals on `E`. -/

/-- An element's three limbs. -/
noncomputable def limbs (e : E) : K × K × K :=
  ((toE_surjective e).choose, (toE_surjective e).choose_spec.choose,
    (toE_surjective e).choose_spec.choose_spec.choose)

theorem limbs_spec (e : E) : toE (limbs e).1 (limbs e).2.1 (limbs e).2.2 = e :=
  (toE_surjective e).choose_spec.choose_spec.choose_spec

theorem limbs_toE (a b c : K) : limbs (toE a b c) = (a, b, c) := by
  obtain ⟨h0, h1, h2⟩ := toE_injective _ _ _ _ _ _ (limbs_spec (toE a b c))
  ext <;> simp [h0, h1, h2]

theorem limbs_add (e e' : E) :
    limbs (e + e') = ((limbs e).1 + (limbs e').1, (limbs e).2.1 + (limbs e').2.1, (limbs e).2.2 + (limbs e').2.2) := by
  conv_lhs => rw [← limbs_spec e, ← limbs_spec e', toE_add, limbs_toE]

theorem coeff_add' (x y : K) (i : ℕ) : coeff (x + y) i = coeff x i + coeff y i := by
  unfold coeff
  split <;> simp [map_add]

theorem coeff_zero' (i : ℕ) : coeff (0 : K) i = 0 := by
  unfold coeff
  split <;> simp

/-- The functional of a mask: `Σ_t mask_t · coordinate_t`, the coordinates the limbs' bits. -/
noncomputable def phi (m : W3) : E →+ ZMod 2 where
  toFun e := ∑ t ∈ range 64, (bitZ m.1 t * coeff (limbs e).1 t + bitZ m.2.1 t * coeff (limbs e).2.1 t +
    bitZ m.2.2 t * coeff (limbs e).2.2 t)
  map_zero' := by
    have h0 : limbs 0 = (0, 0, 0) := by
      rw [← limbs_toE 0 0 0]
      congr 1
      simp [toE, emb_zero]
    simp [h0, coeff_zero']
  map_add' e e' := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun t _ => ?_
    rw [limbs_add]
    simp only [coeff_add']
    ring

/-- Parity by halving: `x`'s bits below `2^k` folded by `xor`. -/
def parH : ℕ → ℕ → ℕ
  | 0, x => x % 2
  | k + 1, x => parH k (x % 2 ^ 2 ^ k ^^^ x / 2 ^ 2 ^ k)

theorem bitZ_xor (a b i : ℕ) : bitZ (a ^^^ b) i = bitZ a i + bitZ b i := by
  simp only [bitZ, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> decide

theorem bitZ_and (a b i : ℕ) : bitZ (a &&& b) i = bitZ a i * bitZ b i := by
  simp only [bitZ, Nat.testBit_and]
  cases a.testBit i <;> cases b.testBit i <;> simp

theorem sum_bitZ_parH : ∀ (k x : ℕ), ∑ t ∈ range (2 ^ k), bitZ x t = bitZ (parH k x) 0
  | 0, x => by rw [pow_zero, sum_range_one]; simp only [parH, bitZ, Nat.testBit_zero, Nat.mod_mod]
  | k + 1, x => by
    rw [parH, ← sum_bitZ_parH k, pow_succ, mul_two, sum_range_add, ← sum_add_distrib]
    refine sum_congr rfl fun t ht => ?_
    rw [bitZ_xor]
    congr 1
    · simp [bitZ, Nat.testBit_mod_two_pow, mem_range.mp ht]
    · simp only [bitZ, Nat.testBit_div_two_pow, add_comm t]

/-- A mask's functional at three limb words: the parities of the masked limbs. -/
def parE (m w : W3) : ℕ := parH 6 (m.1 &&& w.1) ^^^ parH 6 (m.2.1 &&& w.2.1) ^^^ parH 6 (m.2.2 &&& w.2.2)

theorem phi_evW (m w : W3) (hw : w.lt = true) : phi m (evW w) = bitZ (parE m w) 0 := by
  obtain ⟨h0, h1, h2⟩ := (W3.lt_iff w).mp hw
  simp only [phi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, evW, limbs_toE, coeff_ev _ _ h0, coeff_ev _ _ h1,
    coeff_ev _ _ h2, ← bitZ_and, sum_add_distrib, parE, bitZ_xor]
  rw [show (64 : ℕ) = 2 ^ 6 by norm_num, sum_bitZ_parH, sum_bitZ_parH, sum_bitZ_parH]

/-- A dual basis of the fixed coordinates' eq weights: mask `j`'s functional is `1` at weight `j` and `0` at the
others. -/
def dualWords : List W3 := [
  (12513498184927040849, 16362503964058782735, 0), (16374109972837758767, 16158403381256100373, 0),
  (13081939022825805273, 4889128789092015972, 0), (15261255989375862723, 9064137189604270687, 0),
  (11758293010132015049, 15439058959212520134, 0), (12745997890055561693, 14940911238707640744, 0),
  (17582753123372560621, 1133408599174567148, 0), (553247424436713207, 10590496138751144741, 0),
  (3556968117679012085, 3081971772166669260, 0), (2693554758758004249, 5356523217224188601, 0),
  (6940846798224137553, 2183621024419627206, 0), (2115163621779854879, 2133795387450526923, 0),
  (854916015037195601, 1693886468751951903, 0), (4476260710504142917, 9207983434848953537, 0),
  (18345971890047657093, 1628512886214630634, 0), (4454711845892143303, 9495157225958227894, 0),
  (4314102570072388865, 9357135744906985759, 0), (8892880323308671711, 11928191382457878025, 0),
  (3794377589244054361, 2062606950546537568, 0), (5664639063816594887, 15398137982615057846, 0),
  (5403582771371968565, 10721074084881327782, 0), (15051834890440924083, 1744832750099508057, 0),
  (15449753000009614719, 14275944002046490594, 0), (9407838088431172943, 12093696743283630136, 0),
  (11581075229190826613, 11077050542395444695, 0), (8725786693515172349, 14652210067365076997, 0),
  (4778720202834219679, 17857606544450496194, 0), (3260950337530685233, 16004467994472318018, 0),
  (14736506110692878973, 7042657088981559825, 0), (7731813745714426603, 12154523377224730822, 0),
  (9201186587682477515, 1770363062187160141, 0), (7022582292426842981, 7455244480940870570, 0),
  (14632225867638025255, 12816551924197492171, 0), (14922754238821409045, 8828175851443774910, 0),
  (4437212308701418047, 14210079676385370556, 0), (4104733798700744939, 7697954119661007496, 0),
  (213808949947257629, 18333193696509652902, 0), (17431322673102338571, 722619276952705013, 0),
  (8264215589957040187, 16390525466712317837, 0), (32214540187060515, 12082756897219471087, 0),
  (14854640974396962595, 3164818275580802591, 0), (2180740818267789103, 1043035712660669532, 0),
  (10774394855492673425, 16944843123871527957, 0), (6927244783642590071, 2798472842782952161, 0),
  (9320191777506194357, 2647525143296196436, 0), (1643077638595007349, 14978168060610875882, 0),
  (14708180470003757739, 10175965383158429056, 0), (3250600583382513935, 15428574290893845482, 0),
  (3622250032376796549, 2629346876076071017, 0), (5179900433239641053, 5673904747605159082, 0),
  (3527895685971710931, 9331208050692261712, 0), (3196503810524569559, 2175881918950439129, 0),
  (12638054880313957527, 1720584851395921622, 0), (3025417303028994139, 10225556053013227830, 0),
  (7980321223796115125, 6935282095853731281, 0), (1287484738444552421, 4410724045036611460, 0),
  (13755863813184653823, 10651176074336828031, 0), (2465492992549034889, 16966496377177345345, 0),
  (13342044978222768167, 8920652231347317380, 0), (11655729129371461921, 9421592723935020117, 0),
  (6843199056987292857, 5290678403538798521, 0), (10552306491704747887, 12081107503558212753, 0),
  (17441413117570728899, 15592283902952824582, 0), (3928753046405170471, 17271277761636564724, 0),
  (15525336164134224621, 11681008336756386192, 0), (8168623293801321191, 17354391638207082428, 0),
  (10863701806071062507, 11684400920876472740, 0), (2935171760521608405, 15072796219404982036, 0),
  (9213073038663557741, 6326865509818162830, 0), (14462279821912171661, 1090897746386166385, 0),
  (719618173100501783, 16961489445077477487, 0), (389863675457983771, 11406423411833688803, 0),
  (5815330867281254317, 5160380650098141404, 0), (5901998839044721263, 1068239653050085527, 0),
  (4922541088660094903, 7208565528604493754, 0), (9162787819173762897, 6699782221677953844, 0),
  (13007037283569364673, 13576986704997413151, 0), (3735172978759824693, 11444635440258442293, 0),
  (10100770780053316479, 10815562424502227202, 0), (18171599557377085513, 10984503059451706470, 0),
  (17948048251236390231, 5431994837494789665, 0), (17238507669134326183, 13118289246884178425, 0),
  (9594415331840732591, 16928214468425987682, 0), (4349760946087125477, 13388005741719678331, 0),
  (16458450644821551007, 3201213516006436370, 0), (844866510080721457, 7959610906130955619, 0),
  (3847266332680440451, 13725422642173292065, 0), (14495798416955614855, 271808252544364731, 0),
  (11360192533542166225, 6074433778359111702, 0), (11456693726153751077, 10588270577165349501, 0),
  (2124169500624705931, 8433034990335855029, 0), (1218675932072998505, 13060311033662176870, 0),
  (4317974359641481907, 16478912264407510991, 0), (13443012522445398951, 11043071158979408161, 0),
  (7778497240490544053, 14175402550610607858, 0), (5558728969598075067, 8383780712121492842, 0),
  (11769834717478140903, 10881244836474624508, 0), (3993237275283375727, 7600413829266626657, 0),
  (8538604863894504495, 8890293499367018835, 0), (8227668812563343787, 3477567243133094824, 0),
  (5595386356441124097, 17250529721226037218, 0), (6210996834917000765, 11298603591979914203, 0),
  (14795071834641087045, 12637563796012927242, 0), (7942622548281073883, 9470621057467108352, 0),
  (4684652249680926059, 11395651583659031546, 0), (16188911826677539889, 5740643226918278172, 0),
  (526233007307082763, 9007303085910847327, 0), (15428227606498274859, 672355135683420043, 0),
  (10618195416715950553, 9038462883926694060, 0), (8005005076477035877, 7458453609956665911, 0),
  (14330525896474880163, 18013329497445276850, 0), (12051400402936849577, 2856464731132911713, 0),
  (260903365583300893, 14092516436474463441, 0), (11979791072723106835, 10087390075228432193, 0),
  (15528718189170620673, 16218242716079253457, 0), (13121617545401958679, 8890963956912494500, 0),
  (13220144981970551807, 571471251958282735, 0), (8257200114981211099, 13279038448434084928, 0),
  (3149541184762384197, 8318203648129234647, 0), (13330219272268125613, 2384136653459456540, 0),
  (18211903899197626671, 2271105247520200931, 0), (11188016155789267425, 3634214659099622823, 0),
  (17614144305814184643, 6468660195059540742, 0), (10700852463695315193, 12390886154132333162, 0),
  (9241550591223023353, 8022136710489566692, 0), (17100882469543522745, 17676763499288567225, 0),
  (6090204395338377821, 11253039403263717418, 0), (849293939117914349, 5038237135208940307, 0)]

/-- Mask `m` (place `j`) against the weights from place `u`: its functional's parity is `[j = u]` at each. -/
def rowCheck (m : W3) (j : ℕ) : List W3 → ℕ → Bool
  | [], _ => true
  | w :: ws, u => (parE m w % 2 == if j = u then 1 else 0) && rowCheck m j ws (u + 1)

theorem rowCheck_sem {m : W3} {j : ℕ} : ∀ (ws : List W3) (u : ℕ), rowCheck m j ws u = true →
    ∀ k < ws.length, parE m (ws.getD k (0, 0, 0)) % 2 = if j = u + k then 1 else 0
  | [], _, _, k, hk => by simp at hk
  | w :: ws, u, h, k, hk => by
    simp only [rowCheck, Bool.and_eq_true, beq_iff_eq] at h
    rcases k with _ | k
    · simpa using h.1
    · rw [List.getD_cons_succ, rowCheck_sem ws (u + 1) h.2 k (by simpa using hk), show u + 1 + k = u + (k + 1) by ring]

/-- The fixed coordinates' `128` eq weights as limb words, weight `u` taking bit `j` of `u` for coordinate `j`
(`eqv_fixedPt`). -/
def eqWords : List W3 := [
  (14144082947725862126, 4846755567238486821, 11843230004600988457),
  (10810913627372229789, 556142986425226783, 3889330451756464043),
  (11021944648820373656, 10028660408887523956, 1272310714648081991),
  (7872703532120839374, 10347173606095714108, 1885400864893864571),
  (1073663807529717631, 6751947424258138636, 12770108085760217830),
  (7750528209894827630, 1253529329881366556, 11978646371343964044),
  (13246085088310310804, 7464695554289387185, 9758933647331900278),
  (13277300337572243683, 754005015284568953, 17002493046595881509),
  (4185331606802932646, 4415046527535679662, 4441130726942202266),
  (16722835722506176198, 13792327287197519169, 14945826585998280018),
  (4760921920299011872, 2845737156542669052, 899100133133481447),
  (2129424963409002542, 8112174315574583339, 2587378127709389121),
  (4318099829906959071, 11395211787907496996, 1430068136439198604),
  (12963347240778546169, 7270575158402025234, 4244998258542613397),
  (8906152037053376558, 901492109277214113, 8745787388848831353),
  (4572405526330026316, 714043715240064442, 10170191409264482806),
  (10204996935652485341, 7076697675898071494, 10533555988808125478),
  (12332529884066545965, 9832041571252472876, 17335155489316049307),
  (8526171913781238841, 4751879204650596020, 9594275897357386985),
  (9301525308619589149, 6777430687932379169, 16436506365584674971),
  (5083326272991080706, 12752309673689604160, 13577395871488499980),
  (1101058515406289383, 1588846354364496686, 3118049144053147356),
  (2765281603818818897, 1330140773861586154, 11326160258840731312),
  (14569475383351546697, 16967308728261862783, 8996575583765244096),
  (10987181079931267500, 12714614601967087540, 8440731630343318843),
  (3547792149585900592, 1563139427585875919, 6556676300440305931),
  (6683578537895255001, 8864055239884414019, 3877163269170201143),
  (11511673797524396482, 13989525001369046125, 2841907251600556352),
  (9910495133478552181, 78290023388894203, 8812243429762059319),
  (5113028220927850042, 4109191968908267546, 9777647480030335953),
  (16825420714705118689, 11344815273271440828, 5346045185475165378),
  (2313947864696530291, 3192436118250801686, 5373621438197869173),
  (10203426086679622935, 273124797551486227, 16263865552207607222),
  (17707594962187996298, 9812903249217204887, 11871315911658754429),
  (12225843010679096015, 18159039467337143966, 12385054641408258484),
  (7394793238394095807, 12875866105526609207, 2376714675835762794),
  (1421971228107644913, 6721247510065641533, 709956464829701351),
  (13067979528514425760, 15165200766426515143, 124683158955560735),
  (14451148691256472573, 1326415825600169857, 16486058939830772007),
  (14540534910319153677, 17885376088451661972, 9557444155983523592),
  (13332122482349040588, 13173762869622137605, 2132733533071585109),
  (11367365935454378915, 4331998821927908264, 8290925532460858970),
  (13415987221642511908, 12410994283947508969, 12014404563641558175),
  (12945128972786991865, 14567566592215837473, 7601900312703823029),
  (10347638189746643186, 3358873814874223143, 9620437594229987126),
  (11894659403076704688, 14668363599955695129, 5036614731140989361),
  (17925268032177429075, 3085499380285893935, 5303688683972588324),
  (6571263934331816801, 2656046691190154349, 17368215775113720928),
  (6885778367518764018, 5451867544283295198, 17874084240675080351),
  (17184561577759064222, 5446833359986293524, 3770306590342929235),
  (14902989296298927728, 11442990397716714493, 2905321386151896192),
  (3643055004366029388, 8978765986220116123, 8582889426801091637),
  (2557726504830623438, 1916629664455576610, 5476874494180696750),
  (146496834966542231, 4677445604135320684, 12190203232158122974),
  (3941739283986626310, 18429391677735030933, 10690307178912902098),
  (17762243965497701258, 17230844288086617842, 1730901921248280204),
  (7972192304160375001, 3273808478575408188, 8346375613253597460),
  (9787056494893132955, 1794106673932580427, 15045186236189214575),
  (7321281026181454276, 10058086834036872133, 4993762580904259590),
  (14426354552683783328, 9797945445690436859, 14545563906963208968),
  (59033434791201288, 15087098080115945345, 11969856740387649934),
  (17373856439604712876, 11543151273288318923, 13413828408785766558),
  (11457488674870381694, 8084274879208666994, 3783361524772878982),
  (10424737519691163618, 5246805574783599757, 14127335845760478532),
  (12136297795030333408, 12792120342411726068, 15948216025049266649),
  (6062845776473734601, 1773406738689609458, 6136035343031593394),
  (967968169926185288, 4077668911567296019, 7444384047882411816),
  (6741686044738531445, 5094331497636638761, 16514622462370422442),
  (16309446843746184462, 1451430388344269006, 4720804537210615656),
  (18090282051918177744, 13872301098263380939, 4029896084791536726),
  (9146860018338447788, 13207692576620136985, 4708530536775152429),
  (7284686492627060966, 9142307186217632371, 3610787842785833362),
  (10792058762963118241, 9949511508929080968, 14857507240933610339),
  (17478757663743839399, 16324060051316360376, 14646495376240176625),
  (7795907642765108415, 12114325413475438303, 2391622990005108428),
  (9871217902370925318, 12628778962102130574, 14062059095332836934),
  (119067243559570673, 2482318943597778018, 17850534838936720408),
  (7632849567391789887, 5178825827030689004, 8611569677290637810),
  (16030510932552545257, 4542863380954879516, 13840691872216184165),
  (7566194336136346560, 8378658021044492024, 8138829240146506063),
  (11223482508721402718, 16765567611400296900, 9191588253765914875),
  (17842880800935735096, 13809465792095729513, 17875236825358972442),
  (4075768467181147162, 2775852498666294034, 2937930228769813811),
  (8775997044845009015, 14401200382559187778, 9225770274666547469),
  (12979420778500090243, 1286288687756927851, 6021401094247987802),
  (2738832967239427987, 18181284586747004909, 17930578393651657809),
  (17684368775009198157, 14366301661448789489, 16298643279997871457),
  (9724561053661587897, 12112461062989219865, 6413005914966925610),
  (6224833832860314862, 5814295628532765049, 12850922887840897326),
  (17254519915191432242, 13006733213146284866, 2161689687017018773),
  (12831358231885268166, 12151890466675625966, 1724855121314394522),
  (17949044283319712652, 5688881091740751173, 9553552935436763578),
  (11536752491838837685, 745484212390471370, 9696012754609168215),
  (11269764202355435522, 4847108011196875296, 10531778375421114277),
  (9416209219620030138, 13997467361684947102, 4908626651030623149),
  (3439844656625814297, 12101229669496294364, 3910315304232513484),
  (8902762808193814266, 11460147483141363068, 926122471833314575),
  (8283902907161215932, 10973805596509771792, 8853423642737655531),
  (6245163414203236134, 1077762673068297469, 14850016385328617830),
  (309561335427059885, 9832276118462565339, 7548317976457224605),
  (8409465207784601903, 2754636797113521373, 11241902698999292791),
  (8099146739981397564, 15907844471191461014, 179720710391409376),
  (605618028310710416, 1226160611260806257, 13888324449319755113),
  (1004596104981593344, 13856934844647985288, 5004460266854447625),
  (12291128925159817017, 364214772789219699, 306192995102700572),
  (18127719565027648207, 7190690564447000593, 14586793358364538561),
  (15456179999612394776, 4882038179245797020, 9983840123908487958),
  (16143546939334017025, 13747013606888486309, 3943922957091581138),
  (16302784327393991474, 915129474155237404, 15087342505057474082),
  (3281680429538953593, 12761901364459005839, 17474649638586868038),
  (4181990182993256642, 2965187897307493244, 15964158663378874276),
  (7039999895727595957, 2550918678496708129, 13429491822907967014),
  (17159647558558695717, 4789489493252797308, 17991043180306817708),
  (12737042407488359307, 15955609514466349221, 1765297831374962980),
  (599016979980983860, 3842842454380374498, 11311910012208845486),
  (9148295872843594337, 3977604057135775819, 14177356348144382239),
  (10348654329499237449, 10051947576693795217, 10005667744682910643),
  (11229489893926790564, 1522782333274876536, 12487119995431747627),
  (11250222263681083256, 18266980601292049307, 14997466397941430791),
  (12154233416062121243, 8882689727564063106, 14254907854901894112),
  (14324179289946464331, 2621346391425488831, 2806309417316409366),
  (7988673303951694892, 1549753209760197144, 12723494024831188912),
  (7925979104718533372, 13046740006591624579, 7802676767407329600),
  (3948291517131562566, 9331993731450404536, 13097260645948534024),
  (2078617581674411412, 5079114409524449399, 11970496653665274939),
  (4592822283606485857, 16359320038051269832, 1176353909278396711),
  (11948442875586126404, 1992289418840666867, 14904514649709287780),
  (13787267693346314559, 2495614534241249097, 17263583065541652530)]

/-- The small coordinates' `8` eq weights, each in `K` (`eqWs smallWords`). -/
def smallEq : List W3 := [(16714968798032636821, 0, 0), (934417933708345562, 0, 0), (5052831051185709274, 0, 0),
  (13279093613986655126, 0, 0), (13223555727402814747, 0, 0), (11783116775381248671, 0, 0),
  (5077413140227349504, 0, 0), (5126299509413911430, 0, 0)]

/-- The medium coordinates' `16` eq weights (`eqWs medWords`). -/
def medEq : List W3 := [
  (14775659366607399491, 7023206629190432682, 16266491314732473479),
  (4719685174800169514, 3055874001230380565, 6608918478170872),
  (8386123686061483305, 12271425939118320004, 8457235601006491759),
  (7807085247715879770, 10793007157764611102, 13850890827199522326),
  (1203909408158883404, 11545938080379624898, 11968506277768704194),
  (11832747263157671106, 565968541957329433, 15683319305788426470),
  (12460628003107603077, 12176054974993957765, 18041822124408006487),
  (13456319895360808222, 8094947649476402940, 14067963581762442151),
  (12546462775073221248, 14558626449658595155, 1098372873300117608),
  (6675499830380534872, 4693935107876897547, 15544533101281120216),
  (14751659771980093423, 3791678956058830739, 4528943442861660319),
  (7169605683744395650, 3371993204858365752, 6498445984339306504),
  (6547440619632590926, 12281329962722322168, 14654749419549052392),
  (17544319365263872979, 3181866948117303445, 3915636151764405247),
  (613493203397797237, 9648005908868080512, 10055183998552719942),
  (14610315613573444947, 11029569588069449625, 15629172176979777444)]

/-- An element times a `K` word, limb by limb (`toE_smul`). -/
def smulW (a : W3) (k : ℕ) : W3 := (mul a.1 k, mul a.2.1 k, mul a.2.2 k)

theorem evW_smul (a : W3) {k : ℕ} (hk : k < 2 ^ 64) : evW (smulW a k) = evW a * emb (ev k) := by
  rw [evW, evW, smulW, toE_smul]
  simp only [ev_mul _ _ hk]

theorem smallEq_eq : eqWs smallWords = smallEq := by decide +kernel

theorem medEq_eq : eqWs medWords = medEq := by decide +kernel

/-- Weights `lo` to `lo + 31`: weight `u` is medium weight `u / 8` times small weight `u % 8`. -/
def eqChunk (lo : ℕ) : Bool := (List.range 32).all fun d =>
  eqWords.getD (lo + d) (0, 0, 0) ==
    smulW (medEq.getD ((lo + d) / 8) (0, 0, 0)) (smallEq.getD ((lo + d) % 8) (0, 0, 0)).1

theorem eChunk0 : eqChunk 0 = true := by decide +kernel
theorem eChunk1 : eqChunk 32 = true := by decide +kernel
theorem eChunk2 : eqChunk 64 = true := by decide +kernel
theorem eChunk3 : eqChunk 96 = true := by decide +kernel

theorem eq_rows (u : ℕ) (hu : u < 128) :
    eqWords.getD u (0, 0, 0) = smulW (medEq.getD (u / 8) (0, 0, 0)) (smallEq.getD (u % 8) (0, 0, 0)).1 := by
  have h : ∀ k < 4, eqChunk (32 * k) = true := fun k hk => by
    interval_cases k
    exacts [eChunk0, eChunk1, eChunk2, eChunk3]
  have := h (u / 32) (by omega)
  simp only [eqChunk, List.all_eq_true, List.mem_range, beq_iff_eq] at this
  have := this (u % 32) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at this

/-- Masks `lo` to `lo + 15` against every weight. -/
def dualChunk (lo : ℕ) : Bool :=
  (List.range 16).all fun d => rowCheck (dualWords.getD (lo + d) (0, 0, 0)) (lo + d) eqWords 0

theorem dChunk0 : dualChunk 0 = true := by decide +kernel
theorem dChunk1 : dualChunk 16 = true := by decide +kernel
theorem dChunk2 : dualChunk 32 = true := by decide +kernel
theorem dChunk3 : dualChunk 48 = true := by decide +kernel
theorem dChunk4 : dualChunk 64 = true := by decide +kernel
theorem dChunk5 : dualChunk 80 = true := by decide +kernel
theorem dChunk6 : dualChunk 96 = true := by decide +kernel
theorem dChunk7 : dualChunk 112 = true := by decide +kernel

theorem dual_rows (j : ℕ) (hj : j < 128) : rowCheck (dualWords.getD j (0, 0, 0)) j eqWords 0 = true := by
  have h : ∀ k < 8, dualChunk (16 * k) = true := fun k hk => by
    interval_cases k
    exacts [dChunk0, dChunk1, dChunk2, dChunk3, dChunk4, dChunk5, dChunk6, dChunk7]
  have := h (j / 16) (by omega)
  simp only [dualChunk, List.all_eq_true, List.mem_range] at this
  have := this (j % 16) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at this

/-- The fixed coordinates' other facts on words: their limbs and those of `1 +` each below `2^64`, the small weights
in `K`, and every weight's limbs below `2^64`. -/
def fixedOk : Bool :=
  smallWords.length == 3 && medWords.length == 4 && fixedWords.all (fun a => a.lt && a.onePlus.lt) &&
    smallEq.all (fun w => w.lt && w.2.1 == 0 && w.2.2 == 0) && medEq.all W3.lt && eqWords.all W3.lt &&
    eqWords.length == 128

theorem fixedOk_eq : fixedOk = true := by decide +kernel

theorem fixed_facts : smallWords.length = 3 ∧ medWords.length = 4 ∧
    (∀ a ∈ fixedWords, a.lt = true ∧ a.onePlus.lt = true) ∧
    (∀ w ∈ smallEq, w.lt = true ∧ w.2.1 = 0 ∧ w.2.2 = 0) ∧ (∀ w ∈ eqWords, w.lt = true) ∧ eqWords.length = 128 := by
  have h := fixedOk_eq
  simp only [fixedOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, fun w hw => ⟨(h4 w hw).1.1, (h4 w hw).1.2, (h4 w hw).2⟩, h6, h7⟩

/-- The fixed coordinates. -/
noncomputable def fixedPt (j : Fin 7) : E := ew (fixedWords.getD j (0, 0, 0))

theorem eqv_append {a b : ℕ} (p x : Fin a → E) (q y : Fin b → E) :
    eqv (Fin.append p q) (Fin.append x y) = eqv p x * eqv q y := by
  simp only [eqv, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

/-- Row `2^a c + j`'s bits: `j`'s `a`, then `c`'s. -/
theorem bitPoint_add (a b c j : ℕ) (hj : j < 2 ^ a) :
    bitPoint (a + b) (2 ^ a * c + j) = Fin.append (bitPoint a j) (bitPoint b c) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.append_left]
    simp only [bitPoint, Fin.val_castAdd, Nat.testBit_two_pow_mul_add c hj, if_pos i.isLt]
  · rw [Fin.append_right]
    simp only [bitPoint, Fin.val_natAdd, Nat.testBit_two_pow_mul_add c hj, if_neg (show ¬ a + (i : ℕ) < a by omega),
      Nat.add_sub_cancel_left]

/-- The eq weights of coordinates on words, as field elements. -/
theorem eqv_eqWs (as : List W3) (hb : ∀ a ∈ as, a.lt = true ∧ a.onePlus.lt = true) (p : Fin as.length → E)
    (hp : ∀ j, p j = evW (as.getD j (0, 0, 0))) (u : ℕ) (hu : u < 2 ^ as.length) :
    eqv p (bitPoint as.length u) = evW ((eqWs as).getD u (0, 0, 0)) := by
  rw [eqWs_eq, List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; exact hu),
    List.getElem_map, List.getElem_range, evW_eqW as hb, eqv, ← Fin.prod_univ_eq_prod_range]
  refine prod_congr rfl fun j _ => ?_
  rw [hp j]
  by_cases h : u.testBit j <;> simp [bitPoint, h, sub_eq_addE]

theorem eqv_fixedPt (u : ℕ) (hu : u < 128) : eqv fixedPt (bitPoint 7 u) = evW (eqWords.getD u (0, 0, 0)) := by
  obtain ⟨hs, hm, hfa, hse, -, -⟩ := fixed_facts
  have hsb : ∀ a ∈ smallWords, a.lt = true ∧ a.onePlus.lt = true := fun a ha =>
    hfa a (List.mem_append_left _ ha)
  have hmb : ∀ a ∈ medWords, a.lt = true ∧ a.onePlus.lt = true := fun a ha =>
    hfa a (List.mem_append_right _ ha)
  have hfix : (fixedPt : Fin (3 + 4) → E) =
      Fin.append (fun j : Fin 3 => fixedPt (Fin.castAdd 4 j)) (fun j : Fin 4 => fixedPt (Fin.natAdd 3 j)) :=
    (Fin.append_castAdd_natAdd (m := 3) (n := 4) (f := fixedPt)).symm
  have hsmall : eqv (fun j : Fin 3 => fixedPt (Fin.castAdd 4 j)) (bitPoint 3 (u % 8)) =
      evW (smallEq.getD (u % 8) (0, 0, 0)) := by
    rw [← smallEq_eq]
    refine eqv_eqWs smallWords hsb _ (fun j => ?_) (u % 8) (by rw [hs]; omega)
    have hj : (j : ℕ) < smallWords.length := j.isLt
    have hfj : fixedWords.getD j (0, 0, 0) = smallWords.getD j (0, 0, 0) := List.getD_append _ _ _ _ hj
    show ew (fixedWords.getD (j : ℕ) (0, 0, 0)) = _
    rw [hfj, ew_eq_evW (by rw [List.getD_eq_getElem _ _ hj]; exact (hsb _ (List.getElem_mem _)).1)]
  have hmed : eqv (fun j : Fin 4 => fixedPt (Fin.natAdd 3 j)) (bitPoint 4 (u / 8)) =
      evW (medEq.getD (u / 8) (0, 0, 0)) := by
    rw [← medEq_eq]
    refine eqv_eqWs medWords hmb _ (fun j => ?_) (u / 8) (by rw [hm]; omega)
    have hj : (j : ℕ) < medWords.length := j.isLt
    have hfj : fixedWords.getD (3 + j) (0, 0, 0) = medWords.getD j (0, 0, 0) := by
      rw [fixedWords, List.getD_append_right _ _ _ _ (by rw [hs]; omega), hs, Nat.add_sub_cancel_left]
    show ew (fixedWords.getD (3 + (j : ℕ)) (0, 0, 0)) = _
    rw [hfj, ew_eq_evW (by rw [List.getD_eq_getElem _ _ hj]; exact (hmb _ (List.getElem_mem _)).1)]
  have hu' : u = 2 ^ 3 * (u / 8) + u % 8 := by omega
  have hsd := hse _ (List.getElem_mem (show u % 8 < smallEq.length by simp [smallEq]; omega))
  rw [← List.getD_eq_getElem _ (0, 0, 0)] at hsd
  obtain ⟨hlt, h1, h2⟩ := hsd
  obtain ⟨hl0, -, -⟩ := (W3.lt_iff _).mp hlt
  show eqv (fixedPt : Fin (3 + 4) → E) (bitPoint (3 + 4) u) = _
  rw [hfix, hu', bitPoint_add 3 4 _ _ (by omega), eqv_append, hsmall, hmed, ← hu', eq_rows u hu,
    evW_smul _ hl0]
  rw [mul_comm]
  congr 1
  rw [evW, h1, h2, ev_zero, Model.toE_emb]

/-- The fixed coordinates' `128` eq weights are linearly independent over `GF(2)`: no nonempty set of them sums to
zero. -/
theorem fixed_indep (T : Finset ℕ) (hT : T ⊆ range 128) (h : ∑ u ∈ T, eqv fixedPt (bitPoint 7 u) = 0) : T = ∅ := by
  obtain ⟨-, -, -, -, hwl, hwlen⟩ := fixed_facts
  rw [Finset.eq_empty_iff_forall_notMem]
  intro j hj
  have hj128 := mem_range.mp (hT hj)
  have hd := rowCheck_sem eqWords 0 (dual_rows j hj128)
  have hphi := congrArg (phi (dualWords.getD j (0, 0, 0))) h
  rw [map_sum, map_zero] at hphi
  rw [sum_congr rfl fun u hu => by
    have hu128 := mem_range.mp (hT hu)
    have hwlt : (eqWords.getD u (0, 0, 0)).lt = true := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hwl _ (List.getElem_mem _)
    rw [eqv_fixedPt u hu128, phi_evW _ _ hwlt, bitZ, Nat.testBit_zero, hd u (by omega), zero_add]] at hphi
  rw [sum_eq_single j (fun u _ hu => by simp [Ne.symm hu]) (fun h' => absurd hj h')] at hphi
  simp at hphi

/-! The fixed coordinates' event. -/

theorem bitPoint_append (n' c j : ℕ) (hj : j < 128) :
    bitPoint (7 + n') (128 * c + j) = Fin.append (bitPoint 7 j) (bitPoint n' c) :=
  bitPoint_add 7 n' c j (lt_of_lt_of_eq hj (by norm_num))

/-- Slice `j`'s weighted rows over the drawn coordinates `ρ`, the fixed ones summed out. -/
noncomputable def fixedFold (T : Tables) (j c : ℕ) : E :=
  ∑ l ∈ range 128, eqv fixedPt (bitPoint 7 l) * bitE (T.row (j + 64 * (128 * c + l)))

theorem rowSum_append (n' : ℕ) (ρ : Fin n' → E) (T : Tables) (j : ℕ) :
    rowSum (7 + n') (Fin.append fixedPt ρ) T j = ∑ c ∈ range (2 ^ n'), eqv ρ (bitPoint n' c) * fixedFold T j c := by
  rw [rowSum, show 2 ^ (7 + n') = 2 ^ n' * 128 by rw [pow_add]; ring, sum_range_mul]
  refine sum_congr rfl fun c _ => ?_
  rw [fixedFold, mul_sum]
  refine sum_congr rfl fun l hl => ?_
  rw [bitPoint_append n' c l (mem_range.mp hl), eqv_append]
  ring

open Classical in
/-- The fixed coordinates' draw event: some row is broken, yet every slice's weighted rows are zero at
`r = fixed ++ ρ`. -/
noncomputable def fixDraws (n' : ℕ) (T : Tables) : Finset (Fin n' → E) :=
  {ρ | Viol (7 + n') T ∧ ∀ j : Fin 64, rowSum (7 + n') (Fin.append fixedPt ρ) T j = 0}

theorem totalDegree_eqPoly (n : ℕ) (z : ℕ) : (eqPoly n n z).totalDegree ≤ n := by
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  have : ∀ j : Fin n, (if (j : ℕ) < n then (if z.testBit j then MvPolynomial.X j else 1 + MvPolynomial.X j) else 1 :
      MvPolynomial (Fin n) E).totalDegree ≤ 1 := by
    intro j
    split
    · split
      · rw [MvPolynomial.totalDegree_X]
      · exact (MvPolynomial.totalDegree_add _ _).trans
          (max_le (by rw [MvPolynomial.totalDegree_one]; norm_num) (by rw [MvPolynomial.totalDegree_X]))
    · rw [MvPolynomial.totalDegree_one]; norm_num
  calc ∑ j : Fin n, _ ≤ ∑ _j : Fin n, 1 := Finset.sum_le_sum fun j _ => this j
    _ = n := by simp

/-- The fixed coordinates' event is at most an `n'/|E|` fraction of the drawn coordinates `E^n'`: a broken row of slice
`j` leaves `fixedFold` nonzero at its word (`fixed_indep`), so slice `j`'s weighted rows are a nonzero multilinear
polynomial in `ρ` (Schwartz-Zippel). -/
theorem fixDraws_card (n' : ℕ) (T : Tables) : #(fixDraws n' T) * Fintype.card E ≤ n' * Fintype.card E ^ n' := by
  classical
  by_cases hv : Viol (7 + n') T
  swap
  · have : fixDraws n' T = ∅ := by
      ext ρ
      simp [fixDraws, hv]
    rw [this, card_empty, zero_mul]
    exact Nat.zero_le _
  obtain ⟨u, hu, hrow⟩ := hv
  -- The broken row's slice `j`, word `128 c + l`.
  set j := u % 64
  set c := u / 64 / 128
  set l := u / 64 % 128
  have hul : u = j + 64 * (128 * c + l) := by omega
  have hc : c < 2 ^ n' := by
    rw [show 7 + n' + 6 = n' + 13 by ring, pow_add] at hu
    omega
  let H : MvPolynomial (Fin n') E :=
    ∑ c' ∈ range (2 ^ n'), eqPoly n' n' c' * MvPolynomial.C (fixedFold T j c')
  have hH : ∀ ρ, MvPolynomial.eval ρ H = rowSum (7 + n') (Fin.append fixedPt ρ) T j := fun ρ => by
    simp only [H, map_sum, map_mul, MvPolynomial.eval_C, eval_eqPoly_eqv, rowSum_append]
  -- `fixedFold` is nonzero at the broken row's word.
  have hfold : fixedFold T j c ≠ 0 := by
    intro h0
    have hset : fixedFold T j c = ∑ l' ∈ (range 128).filter (fun l' => T.row (j + 64 * (128 * c + l')) = 1),
        eqv fixedPt (bitPoint 7 l') := by
      rw [fixedFold, sum_filter]
      refine sum_congr rfl fun l' _ => ?_
      rcases zmod2_cases (T.row (j + 64 * (128 * c + l'))) with h | h <;> simp [h]
    rw [hset] at h0
    have := fixed_indep _ (filter_subset _ _) h0
    have hl : l ∈ (range 128).filter (fun l' => T.row (j + 64 * (128 * c + l')) = 1) := by
      refine mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩
      rw [← hul]
      rcases zmod2_cases (T.row u) with h | h
      · exact absurd h hrow
      · exact h
    rw [this] at hl
    simp at hl
  have hp : H ≠ 0 := by
    intro h0
    have := congrArg (MvPolynomial.eval (bitPoint n' c)) h0
    simp only [H, map_sum, map_mul, MvPolynomial.eval_C, map_zero] at this
    rw [sum_congr rfl fun z hz => by rw [eval_eqPoly le_rfl (mem_range.mp hz) hc]] at this
    simp [hc] at this
    exact hfold this
  have sz := MvPolynomial.schwartz_zippel_totalDegree hp (univ : Finset E)
  rw [Fintype.piFinset_univ, card_univ] at sz
  have hE : (0 : ℚ≥0) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  rw [div_le_div_iff₀ (by positivity) hE] at sz
  have hdeg : (H.totalDegree : ℚ≥0) ≤ n' := by
    have : H.totalDegree ≤ n' :=
      MvPolynomial.totalDegree_finsetSum_le fun z _ => (MvPolynomial.totalDegree_mul _ _).trans
        (by rw [MvPolynomial.totalDegree_C, add_zero]; exact totalDegree_eqPoly n' z)
    exact_mod_cast this
  have hsub : #(fixDraws n' T) ≤ #({ρ | MvPolynomial.eval ρ H = 0} : Finset (Fin n' → E)) := by
    refine card_le_card fun ρ hρ => ?_
    simp only [fixDraws, mem_filter, mem_univ, true_and] at hρ ⊢
    rw [hH]
    exact hρ.2 ⟨j, by omega⟩
  have : (#({ρ | MvPolynomial.eval ρ H = 0} : Finset (Fin n' → E)) : ℚ≥0) * Fintype.card E ≤
      n' * Fintype.card E ^ n' := sz.trans (by gcongr)
  have : #({ρ | MvPolynomial.eval ρ H = 0} : Finset (Fin n' → E)) * Fintype.card E ≤ n' * Fintype.card E ^ n' := by
    exact_mod_cast this
  exact (Nat.mul_le_mul_right _ hsub).trans this

/-- Off the fixed coordinates' event, zero weighted rows for every slice give every row. -/
theorem no_viol_of_rows {n' : ℕ} {T : Tables} {ρ : Fin n' → E} (hx : ρ ∉ fixDraws n' T)
    (h : ∀ j : Fin 64, rowSum (7 + n') (Fin.append fixedPt ρ) T j = 0) : ¬ Viol (7 + n') T := by
  classical
  intro hv
  exact hx (by simp only [fixDraws, mem_filter, mem_univ, true_and]; exact ⟨hv, h⟩)

/-- The zerocheck's two events together: where its input claim is the round-1 message's polynomial at `ζ` and the
honest instance's sum at `r = fixed ++ ρ`, every row holds off the skip's and the fixed coordinates' events. -/
theorem no_viol_of_claim {n' : ℕ} {ρ : Fin n' → E} {T : Tables} {v : Fin 64 → E} {ζ : E}
    (heq : (phat v).eval ζ = (zeroInst (7 + n') (Fin.append fixedPt ρ) T ζ).sum)
    (hskip : ζ ∉ skipDraws (phat v) (honestP (7 + n') (Fin.append fixedPt ρ) T)) (hfix : ρ ∉ fixDraws n' T) :
    ¬ Viol (7 + n') T :=
  no_viol_of_rows hfix (rows_of_skip heq hskip)

/-! Non-vacuity. -/

/-- The all-zero tables break no row. -/
example (n : ℕ) : ¬ Viol n ⟨0, 0, 0⟩ := by
  rintro ⟨u, -, h⟩
  exact h (by simp [Tables.row])

/-- `c = 1`, `a = b = 0` breaks every row, so the events' hypothesis is met. -/
example (n : ℕ) : Viol n ⟨0, 0, 1⟩ := ⟨0, by positivity, by simp [Tables.row]⟩

/-- The skip's event is not empty: the zero message's polynomial is zero, and meets `X` at `0`. -/
example : (0 : E) ∈ skipDraws (phat 0) X := by
  classical
  have h0 : phat 0 = 0 := phat_unique (by simp) (by simp) (by simp)
  simp only [skipDraws, mem_filter, mem_univ, true_and, h0]
  exact ⟨(X_ne_zero).symm, by simp⟩

/-! Mutation tests of the kernel checks' rules. -/

/-- A node of `Λ` is no root of `V_S`, and `V_S` is zero, not `V_S(λ_0)`, at a node of `S`. -/
example : vanOk 0 (lWords.getD 0 0) = false := by decide +kernel
example : vanOk offWord (sWords.getD 1 0) = false := by decide +kernel

/-- The constants' products read `c_0`: with `c_1` they are not one. -/
example : (mul (mul d128Word offWord) (vc 1) == 1) = false := by decide +kernel
example : (mul d64Word (vc 1) == 1) = false := by decide +kernel

/-- The nodes listed twice are not distinct. -/
example : decide (sWords ++ sWords).Nodup = false := by decide +kernel

/-- Weight `8` is the medium weight `1` times the small weight `0`; the other pairing is not it. -/
example : (eqWords.getD 8 (0, 0, 0) == smulW (medEq.getD 0 (0, 0, 0)) (smallEq.getD 1 (0, 0, 0)).1) = false := by
  decide +kernel

/-- Mask `0` read as place `1`'s fails: its functional is `1` at weight `0`. -/
example : rowCheck (dualWords.getD 0 (0, 0, 0)) 1 eqWords 0 = false := by decide +kernel

end LeanVMCircuits.Rec.Flock
