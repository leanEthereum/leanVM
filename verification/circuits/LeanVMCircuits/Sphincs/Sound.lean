module

public import LeanVMCircuits.Sphincs.SoundGadgets
public import LeanVMCircuits.Sphincs.Statement

@[expose] public section

/-!
# Soundness of the leanSPHINCS circuit

In every assignment the machine accepts the circuit of `n ≤ 2^20` signatures with (`Accepts`: its rows satisfied and
its dynamic bus balanced), statement words `4j .. 4j + 3` encode a root, a public parameter and a message for which
some signature verifies over words (`Sphincs.Words.verify`). The signature is read off the assignment: the
randomizer, the secrets and siblings of the few-time trees, and per layer the counter, the chain elements and the
siblings are the circuit's free wires.

Per signature (`signature_good`): the statement words decode as for leanXMSS; the message digest is its hash row
chain's, and its first three words' splits are the index's and the leaf indices' bits, the last held zero; the
few-time key is `fts_good`'s, each layer `layer_good`'s, and the top layer's root is held equal to the statement's.
Layer `lay` of signature `j` names its 103 `STEP` and 42 `LINK` rows, of tag `3 j + lay` (below `2^22` by the
bound); its chains' ends are `Words.chainFrom`'s when those rows' tuples balance. The rows the layers name are all the
circuit's (`Sphincs.count_circuit`, `rows_perm`), so the balanced bus balances each tag's tuples
(`local_of_balanced`).
-/

namespace LeanVMCircuits.Sphincs

open LeanVMCircuits.Rec (K E toE emb ofWord toWord words4 digest hashWords num root toE_injective)
open LeanVMCircuits.Rec.Model
open LeanVMCircuits.Xmss
open Xmss.Words (W Dig)

/-- One signature's statement words from statement word `b` on. -/
def EncodesAt (st : ℕ → Fin 4 → K) (b : ℕ) (root pp : Dig) (msg : W × W × W × W) : Prop :=
  st b = limbs3 root.1 root.2 0 ∧ st (b + 1) = limbs3 pp.1 pp.2 0 ∧
  st (b + 2) = limbs3 msg.1 msg.2.1 0 ∧ st (b + 3) = limbs3 msg.2.2.1 msg.2.2.2 0

/-- The message digest's first three words as one number. -/
noncomputable def digestValue (val : Val) (d : ℕ) : ℕ :=
  toWord (val d 0) + 2 ^ 64 * toWord (val d 1) + 2 ^ 128 * toWord (val d 2)

theorem pres_union (a b : ℕ) : Pres (union a b) := fun _ => rfl

theorem foldlM_snoc {f : Dig → Fin 3 → Option Dig} {l : List (Fin 3)} {a : Fin 3} {x y z : Dig}
    (h1 : l.foldlM f x = some y) (h2 : f y a = some z) : (l ++ [a]).foldlM f x = some z := by
  rw [List.foldlM_append, h1]
  show [a].foldlM f y = some z
  rw [List.foldlM_cons, h2]
  rfl

theorem testBit_num' (val : Val) (bs : List ℕ) (j : ℕ) (hj : j < 64) :
    (num (fun i => if val (bs.getD i 0) 0 = 1 then 1 else 0) 64).testBit j = true ↔ val (bs.getD j 0) 0 = 1 := by
  rw [Rec.testBit_num _ _ _ hj, decide_eq_true_iff, ite_one]

/-- The bits of three split words, low word first. -/
theorem bits192 (w0 w1 w2 : List ℕ) (val : Val) (A B C : ℕ) (h0 : w0.length = 64) (h1 : w1.length = 64)
    (hA : A = num (fun i => if val (w0.getD i 0) 0 = 1 then 1 else 0) 64)
    (hB : B = num (fun i => if val (w1.getD i 0) 0 = 1 then 1 else 0) 64)
    (hC : C = num (fun i => if val (w2.getD i 0) 0 = 1 then 1 else 0) 64) :
    ∀ i < 192, (val ((w0 ++ w1 ++ w2).getD i 0) 0 = 1 ↔ (A + 2 ^ 64 * B + 2 ^ 128 * C).testBit i = true) := by
  intro i hi
  have hAl : A < 2 ^ 64 := hA ▸ Rec.num_lt _ _
  have hBl : B < 2 ^ 64 := hB ▸ Rec.num_lt _ _
  rw [show A + 2 ^ 64 * B + 2 ^ 128 * C = 2 ^ 64 * (2 ^ 64 * C + B) + A by ring,
    Nat.testBit_two_pow_mul_add _ hAl, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_append, h0, h1]
  by_cases hi0 : i < 64
  · rw [if_pos hi0, if_pos (show i < 64 + 64 by omega), List.getElem?_append_left (by omega),
      ← List.getD_eq_getElem?_getD, hA, testBit_num' val w0 i hi0]
  · rw [if_neg hi0, Nat.testBit_two_pow_mul_add _ hBl]
    by_cases hi1 : i - 64 < 64
    · rw [if_pos hi1, if_pos (show i < 64 + 64 by omega), List.getElem?_append_right (by omega), h0,
        ← List.getD_eq_getElem?_getD, hB, testBit_num' val w1 _ hi1]
    · rw [if_neg hi1, if_neg (show ¬ i < 64 + 64 by omega), ← List.getD_eq_getElem?_getD, hC,
        show i - (64 + 64) = i - 64 - 64 by omega, testBit_num' val w2 _ (by omega)]

/-- The bits `s .. s + h` of a word given by its bits. -/
theorem sub_bits (bs : List ℕ) (val : Val) (V n s h : ℕ) (hsh : s + h ≤ n) (hlen : bs.length = n)
    (hV : ∀ i < n, (val (bs.getD i 0) 0 = 1 ↔ V.testBit i = true))
    (hbool : ∀ i < n, val (bs.getD i 0) 0 = 0 ∨ val (bs.getD i 0) 0 = 1) :
    ((bs.drop s).take h).length = h ∧ V / 2 ^ s % 2 ^ h < 2 ^ h ∧
      (∀ i < h, (val (((bs.drop s).take h).getD i 0) 0 = 1 ↔ (V / 2 ^ s % 2 ^ h).testBit i = true)) ∧
      ∀ i < h, val (((bs.drop s).take h).getD i 0) 0 = 0 ∨ val (((bs.drop s).take h).getD i 0) 0 = 1 := by
  refine ⟨by simp only [List.length_take, List.length_drop, hlen]; omega, Nat.mod_lt _ (by positivity),
    fun i hi => ?_, fun i hi => ?_⟩
  · rw [getD_take' _ _ _ hi, getD_drop', Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and,
      Nat.testBit_div_two_pow, show i + s = s + i by omega]
    exact hV _ (by omega)
  · rw [getD_take' _ _ _ hi, getD_drop']
    exact hbool _ (by omega)

theorem us_getD (bits : List ℕ) (κ : ℕ) (hκ : κ < 15) :
    (((List.range 15).map fun k => (bits.drop (26 + 10 * k)).take 10).getD κ []) =
      (bits.drop (26 + 10 * κ)).take 10 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hκ]
  rfl

theorem lay_mem (lay : ℕ) (hlay : lay < 3) : lay ∈ ([2, 1, 0] : List ℕ).take 3 := by
  interval_cases lay <;> simp

/-- Signature `j`'s verification: its layers' 103 `STEP` and 42 `LINK` rows each, layer `lay`'s of tag
`3 j + lay`, and, when each layer's tuples balance, its statement words encode a key and a message some signature
verifies. -/
theorem signature_good (j : ℕ) (hj : j < 2 ^ 20) : Good (fun _ => True) (Sphincs.Circuit.signature j) fun s _ s' =>
    s'.statement = s.statement + 4 ∧ ∃ Rs Ls : ℕ → List (List ℕ), (∀ lay < 3, (Rs lay).length = 103 ∧
      (Ls lay).length = 42 ∧ (Rs lay).Nodup ∧ (∀ r ∈ Rs lay, r ∈ s'.step) ∧ ∀ r ∈ Ls lay, r ∈ s'.link) ∧
    ∀ st val, Sat st s' val → (∀ lay < 3, SigRows (3 * j + lay) val (Rs lay) (Ls lay)) ∧
      ((∀ lay < 3, LocalBal val (Rs lay) (Ls lay)) → ∃ root pp msg,
        EncodesAt st s.statement root pp msg ∧ ∃ sig, Sphincs.Words.verify root pp msg sig = true) := by
  unfold Sphincs.Circuit.signature
  refine good_of_post fun s hs _ => ?_
  refine statementWords_good1.step hs trivial ?_
  rintro _ s1 hi1 he1 ⟨hst1, rt0, rt1, rfl, hrt0, hrt1, hrtv⟩
  refine statementWords_good1.step hi1 trivial ?_
  rintro _ s2 hi2 he2 ⟨hst2, p0, p1, rfl, hp0, hp1, hpv⟩
  refine statementWords_good1.step hi2 trivial ?_
  rintro _ s3 hi3 he3 ⟨hst3, m0, m1, rfl, hm0, hm1, hmv1⟩
  refine statementWords_good1.step hi3 trivial ?_
  rintro _ s4 hi4 he4 ⟨hst4, m2, m3, rfl, hm2, hm3, hmv2⟩
  refine ((kConst_good 0).pres (pres_kConst 0)).step hi4 trivial ?_
  rintro z s5 hi5 he5 ⟨hst5, hz, hzv⟩
  refine fresh_good'.step hi5 trivial ?_
  rintro rho s6 hi6 he6 ⟨hst6, hrho⟩
  refine (words_good rho).step hi6 (Wires.cons' hrho Wires.nil') ?_
  rintro ⟨r0, r1, r2⟩ s7 hi7 he7 ⟨hst7, hr0, hr1, -, hrv⟩
  try dsimp only
  refine (th_good (Sphincs.Circuit.tweak0 12 0 0) z [p0, p1] ([r0, r1] ++ [rt0, rt1] ++ [m0, m1] ++ [m2, m3])
    (by norm_num)).step hi7 trivial ?_
  rintro d s8 hi8 he8 ⟨hst8, hd, hdv⟩
  refine ((dToK_good d).pres (pres_dToK d)).step hi8 (Wires.cons' hd Wires.nil') ?_
  rintro ks s9 hi9 he9 ⟨hst9, hks, hksv⟩
  refine ((split_good _).pres (pres_split _)).step hi9 trivial ?_
  rintro w0 s10 hi10 he10 ⟨hst10, hw0len, hw0w, hw0v⟩
  refine ((split_good _).pres (pres_split _)).step hi10 trivial ?_
  rintro w1 s11 hi11 he11 ⟨hst11, hw1len, hw1w, hw1v⟩
  refine ((split_good _).pres (pres_split _)).step hi11 trivial ?_
  rintro w2 s12 hi12 he12 ⟨hst12, hw2len, hw2w, hw2v⟩
  have hblen : (w0 ++ w1 ++ w2).length = 192 := by simp [hw0len, hw1len, hw2len]
  have hbw : Wires (w0 ++ w1 ++ w2) s12 := by
    intro w hw
    simp only [List.mem_append] at hw
    rcases hw with (hw | hw) | hw
    · exact lt_mono (hw0w w hw) (by ext_chain)
    · exact lt_mono (hw1w w hw) (by ext_chain)
    · exact hw2w w hw
  have hidxlen : ((w0 ++ w1 ++ w2).take 26).length = 26 := by rw [List.length_take, hblen]; rfl
  have hidxw : Wires ((w0 ++ w1 ++ w2).take 26) s12 := fun w hw => hbw w (List.mem_of_mem_take hw)
  have husw : ∀ κ < 15, Wires ((((List.range 15).map fun k => ((w0 ++ w1 ++ w2).drop (26 + 10 * k)).take 10).getD
      κ [])) s12 := fun κ hκ w hw => by
    rw [us_getD _ κ hκ] at hw
    exact hbw w (List.mem_of_mem_drop (List.mem_of_mem_take hw))
  have huslen : ∀ κ < 15, (((List.range 15).map fun k => ((w0 ++ w1 ++ w2).drop (26 + 10 * k)).take 10).getD
      κ []).length = 10 := fun κ hκ => by
    rw [us_getD _ κ hκ]; simp only [List.length_take, List.length_drop, hblen]; omega
  refine (zeros_good _).step hi12 trivial ?_
  rintro _ s13 hi13 he13 ⟨hst13, hu14⟩
  -- What every later assignment says of the digest's bits.
  have hctx : ∀ st val, Sat st s13 val →
      (∀ i < 192, (val ((w0 ++ w1 ++ w2).getD i 0) 0 = 1 ↔ (digestValue val d).testBit i = true)) ∧
      (∀ i < 192, val ((w0 ++ w1 ++ w2).getD i 0) 0 = 0 ∨ val ((w0 ++ w1 ++ w2).getD i 0) 0 = 1) := by
    intro st val hsat
    obtain ⟨hb0, hn0⟩ := hw0v st val (hsat.mono (by ext_chain))
    obtain ⟨hb1, hn1⟩ := hw1v st val (hsat.mono (by ext_chain))
    obtain ⟨hb2, hn2⟩ := hw2v st val (hsat.mono (by ext_chain))
    have hk0 : val (ks.getD 0 0) 0 = val d 0 := hksv st val (hsat.mono (by ext_chain)) 0
    have hk1 : val (ks.getD 1 0) 0 = val d 1 := hksv st val (hsat.mono (by ext_chain)) 1
    have hk2 : val (ks.getD 2 0) 0 = val d 2 := hksv st val (hsat.mono (by ext_chain)) 2
    rw [hk0] at hn0
    rw [hk1] at hn1
    rw [hk2] at hn2
    refine ⟨bits192 w0 w1 w2 val _ _ _ hw0len hw1len hn0 hn1 hn2, fun i hi => ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_append, List.length_append, hw0len, hw1len]
    by_cases hi0 : i < 64
    · rw [if_pos (show i < 64 + 64 by omega), List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
      exact hb0 i hi0
    · by_cases hi1 : i < 128
      · rw [if_pos (show i < 64 + 64 by omega), List.getElem?_append_right (by omega), hw0len,
          ← List.getD_eq_getElem?_getD]
        exact hb1 _ (by omega)
      · rw [if_neg (show ¬ i < 64 + 64 by omega), ← List.getD_eq_getElem?_getD]
        exact hb2 _ (by omega)
  have hidx : ∀ st val, Sat st s13 val → digestValue val d % 2 ^ 26 < 2 ^ 26 ∧
      (∀ i < 26, (val (((w0 ++ w1 ++ w2).take 26).getD i 0) 0 = 1 ↔
        (digestValue val d % 2 ^ 26).testBit i = true)) ∧
      ∀ i < 26, val (((w0 ++ w1 ++ w2).take 26).getD i 0) 0 = 0 ∨
        val (((w0 ++ w1 ++ w2).take 26).getD i 0) 0 = 1 := by
    intro st val hsat
    obtain ⟨hV, hB⟩ := hctx st val hsat
    obtain ⟨-, h1, h2, h3⟩ := sub_bits (w0 ++ w1 ++ w2) val (digestValue val d) 192 0 26 (by omega) hblen hV hB
    simp only [List.drop_zero, pow_zero, Nat.div_one] at h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hus : ∀ st val, Sat st s13 val → ∀ κ < 15, digestValue val d / 2 ^ (26 + 10 * κ) % 2 ^ 10 < 2 ^ 10 ∧
      (∀ i < 10, (val ((((List.range 15).map fun k => ((w0 ++ w1 ++ w2).drop (26 + 10 * k)).take 10).getD
        κ []).getD i 0) 0 = 1 ↔ (digestValue val d / 2 ^ (26 + 10 * κ) % 2 ^ 10).testBit i = true)) ∧
      ∀ i < 10, val ((((List.range 15).map fun k => ((w0 ++ w1 ++ w2).drop (26 + 10 * k)).take 10).getD
        κ []).getD i 0) 0 = 0 ∨ val ((((List.range 15).map fun k => ((w0 ++ w1 ++ w2).drop (26 + 10 * k)).take 10).getD
        κ []).getD i 0) 0 = 1 := by
    intro st val hsat κ hκ
    obtain ⟨hV, hB⟩ := hctx st val hsat
    obtain ⟨-, h1, h2, h3⟩ := sub_bits (w0 ++ w1 ++ w2) val (digestValue val d) 192 (26 + 10 * κ) 10 (by omega)
      hblen hV hB
    rw [us_getD _ κ hκ]
    exact ⟨h1, h2, h3⟩
  refine (spIndexWord_good ((w0 ++ w1 ++ w2).take 26) [] (by omega) (by simp)).step hi13
    ⟨hidxw.mono (by ext_chain), Wires.nil'⟩ ?_
  rintro top s14 hi14 he14 ⟨hst14, htop, htopv⟩
  refine (fts_good _ _ top p0 p1 hidxlen fun κ hκ => huslen κ (by omega)).step hi14
    ⟨hidxw.mono (by ext_chain), fun κ hκ => (husw κ (by omega)).mono (by ext_chain), htop,
      lt_mono hp0 (by ext_chain), lt_mono hp1 (by ext_chain)⟩ ?_
  rintro msg0 s15 hi15 he15 ⟨hst15, hmsg0, hmsg0v⟩
  -- The layers.
  refine post_bind (forIn_post [2, 1, 0] _ (fun k (m : ℕ) s' => s'.statement = s.statement + 4 ∧ m < s'.next ∧
      ∃ Rs Ls : ℕ → List (List ℕ), (∀ lay ∈ ([2, 1, 0] : List ℕ).take k, (Rs lay).length = 103 ∧
        (Ls lay).length = 42 ∧ (Rs lay).Nodup ∧ (∀ r ∈ Rs lay, r ∈ s'.step) ∧ ∀ r ∈ Ls lay, r ∈ s'.link) ∧
      ∀ st val, Sat st s' val → (∀ lay ∈ ([2, 1, 0] : List ℕ).take k, SigRows (3 * j + lay) val (Rs lay) (Ls lay)) ∧
        ((∀ lay ∈ ([2, 1, 0] : List ℕ).take k, LocalBal val (Rs lay) (Ls lay)) →
        ∃ (ctrs : Fin 3 → W) (tipsF : Fin 3 → ℕ → Dig) (pathsF : Fin 3 → ℕ → Dig),
        ∀ sig : Sphincs.Words.Sig, (∀ q ∈ ([2, 1, 0] : List (Fin 3)).take k, sig.counters q = ctrs q ∧
          (∀ i, sig.tips q i = tipsF q i) ∧ (∀ l (hl : l < Sphincs.Words.height q), sig.paths q ⟨l, hl⟩ = pathsF q l)) →
        (([2, 1, 0] : List (Fin 3)).take k).foldlM (Sphincs.Words.layerRoot (w64 val p0, w64 val p1)
          (digestValue val d % 2 ^ 26) sig) (dig val msg0) = some (dig val m))) hi15
      ⟨by omega, hmsg0, fun _ => [], fun _ => [], fun _ h => absurd h (by simp), fun _ _ _ =>
        ⟨fun _ h => absurd h (by simp), fun _ => ⟨fun _ => 0, fun _ _ => (0, 0), fun _ _ => (0, 0),
          fun _ _ => rfl⟩⟩⟩ ?_) ?_
  · rintro k hk m s16 hi16 he16 ⟨hst16, hm, Rs, Ls, hrows16, hv16⟩
    have hk3 : k < 3 := by simpa using hk
    have hkl : k < ([2, 1, 0] : List ℕ).length := by simpa using hk3
    have hlay : ([2, 1, 0] : List ℕ)[k]'hkl < 3 := by interval_cases k <;> simp
    have hfin : (⟨([2, 1, 0] : List ℕ)[k]'hkl, hlay⟩ : Fin 3) = ([2, 1, 0] : List (Fin 3))[k]'(by simpa using hk3) := by
      interval_cases k <;> rfl
    have hnot : ([2, 1, 0] : List (Fin 3))[k]'(by simpa using hk3) ∉ ([2, 1, 0] : List (Fin 3)).take k := by
      interval_cases k <;> simp (config := { decide := true })
    have htake : ([2, 1, 0] : List (Fin 3)).take (k + 1) =
        ([2, 1, 0] : List (Fin 3)).take k ++ [([2, 1, 0] : List (Fin 3))[k]'(by simpa using hk3)] := by
      interval_cases k <;> rfl
    have hnotN : ([2, 1, 0] : List ℕ)[k]'hkl ∉ ([2, 1, 0] : List ℕ).take k := by
      interval_cases k <;> simp
    have htakeN : ([2, 1, 0] : List ℕ).take (k + 1) = ([2, 1, 0] : List ℕ).take k ++ [([2, 1, 0] : List ℕ)[k]'hkl] := by
      interval_cases k <;> rfl
    have hmemN : ∀ lay, lay ∈ ([2, 1, 0] : List ℕ).take (k + 1) → lay ≠ ([2, 1, 0] : List ℕ)[k]'hkl →
        lay ∈ ([2, 1, 0] : List ℕ).take k := fun lay hl hne => by
      rw [htakeN] at hl
      rcases List.mem_append.mp hl with hl | hl
      · exact hl
      · exact absurd (List.mem_singleton.mp hl) hne
    refine (layer_good j _ hlay (by omega) _ p0 p1 m hidxlen).step hi16 ⟨hidxw.mono (by ext_chain),
      lt_mono hp0 (by ext_chain), lt_mono hp1 (by ext_chain), hm⟩ ?_
    rintro m' s17 hi17 he17 ⟨hst17, hm', R, L, hRl, hLl, hRn, hRm, hLm, hv17⟩
    refine post_pure hi17 (by ext_chain) ⟨m', rfl, by omega, hm', fun x => if x = ([2, 1, 0] : List ℕ)[k]'hkl then R
      else Rs x, fun x => if x = ([2, 1, 0] : List ℕ)[k]'hkl then L else Ls x, fun lay hl => ?_, fun st val hsat => ?_⟩
    · by_cases hx : lay = ([2, 1, 0] : List ℕ)[k]'hkl
      · simp only [if_pos hx]
        exact ⟨hRl, hLl, hRn, hRm, hLm⟩
      · simp only [if_neg hx]
        obtain ⟨h1, h2, h3, h4, h5⟩ := hrows16 lay (hmemN lay hl hx)
        exact ⟨h1, h2, h3, fun r hr => he17.steps _ (h4 r hr), fun r hr => he17.links _ (h5 r hr)⟩
    obtain ⟨hidxlt, hidxb, hidxbool⟩ := hidx st val (hsat.mono (by ext_chain))
    obtain ⟨hR16, hl16⟩ := hv16 st val (hsat.mono he17)
    obtain ⟨hRk, hlk⟩ := hv17 st val hsat
    refine ⟨fun lay hl => ?_, fun hloc => ?_⟩
    · by_cases hx : lay = ([2, 1, 0] : List ℕ)[k]'hkl
      · simp only [if_pos hx]
        rw [hx]
        exact hRk
      · simp only [if_neg hx]
        exact hR16 lay (hmemN lay hl hx)
    obtain ⟨ctrs, tipsF, pathsF, hfold⟩ := hl16 fun lay hl => by
      have hne : lay ≠ ([2, 1, 0] : List ℕ)[k]'hkl := fun h => hnotN (h ▸ hl)
      have := hloc lay (by rw [htakeN]; exact List.mem_append_left _ hl)
      simp only [if_neg hne] at this
      exact this
    obtain ⟨ctr, tips, path, hlr⟩ := hlk (by
      have := hloc (([2, 1, 0] : List ℕ)[k]'hkl) (by rw [htakeN]; exact List.mem_append_right _ (List.mem_singleton_self _))
      simpa using this) _ hidxlt hidxb hidxbool
    rw [hfin] at hlr
    refine ⟨fun q => if q = ([2, 1, 0] : List (Fin 3))[k]'(by simpa using hk3) then ctr else ctrs q,
      fun q => if q = ([2, 1, 0] : List (Fin 3))[k]'(by simpa using hk3) then tips else tipsF q,
      fun q => if q = ([2, 1, 0] : List (Fin 3))[k]'(by simpa using hk3) then path else pathsF q,
      fun sig hag => ?_⟩
    obtain ⟨hc, ht, hp⟩ := hag _ (by rw [htake]; exact List.mem_append_right _ (List.mem_singleton_self _))
    simp only [if_true] at hc ht hp
    rw [htake]
    refine foldlM_snoc (hfold sig fun q hq => ?_) (hlr sig hc (fun i => ht i) hp)
    · have hne : q ≠ ([2, 1, 0] : List (Fin 3))[k]'(by simpa using hk3) := fun h => hnot (h ▸ hq)
      obtain ⟨hc, ht, hp⟩ := hag q (by rw [htake]; exact List.mem_append_left _ hq)
      simp only [if_neg hne] at hc ht hp
      exact ⟨hc, ht, hp⟩
  · rintro msgF s16 hi16 he16 ⟨hst16, hmF, Rs, Ls, hrows16, hv16⟩
    refine ((dToK_good msgF).pres (pres_dToK msgF)).step hi16 (Wires.cons' hmF Wires.nil') ?_
    rintro rs s17 hi17 he17 ⟨hst17, hrs, hrsv⟩
    refine ((union_good _ _).pres (pres_union _ _)).step hi17 trivial ?_
    rintro _ s18 hi18 he18 ⟨hst18, hu0⟩
    refine ((union_good _ _).pres (pres_union _ _)).last hi18 trivial (by ext_chain) ?_
    rintro _ s19 he19 ⟨hst19, hu1⟩
    refine ⟨by omega, Rs, Ls, fun lay hlay => ?_, fun st val hsat => ?_⟩
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hrows16 lay (lay_mem lay hlay)
      exact ⟨h1, h2, h3, fun r hr => (show Ext s16 s19 by ext_chain).steps _ (h4 r hr),
        fun r hr => (show Ext s16 s19 by ext_chain).links _ (h5 r hr)⟩
    obtain ⟨hR16, hl16⟩ := hv16 st val (hsat.mono (by ext_chain))
    refine ⟨fun lay hlay => hR16 lay (lay_mem lay hlay), fun hloc => ?_⟩
    -- Read everything off the final assignment.
    obtain ⟨hidxlt, hidxb, hidxbool⟩ := hidx st val (hsat.mono (by ext_chain))
    have husv := hus st val (hsat.mono (by ext_chain))
    have htop' : w64 val top = tw1 (digestValue val d % 2 ^ 26) 0 :=
      htopv st val (hsat.mono (by ext_chain)) _ 0 (by rw [hidxlen]; exact hidxlt) (by simp) (by rw [hidxlen]; exact hidxb)
        (fun i hi => absurd hi (by simp))
    obtain ⟨secrets, paths, hfts⟩ := hmsg0v st val (hsat.mono (by ext_chain)) (digestValue val d % 2 ^ 26)
      (fun κ => digestValue val d / 2 ^ (26 + 10 * κ) % 2 ^ 10) hidxlt hidxb (fun κ hκ => husv κ (by omega)) htop'
    obtain ⟨ctrs, tipsF, pathsF, hfold⟩ := hl16 fun lay hl => hloc lay (by
      have : lay ∈ ([2, 1, 0] : List ℕ) := by simpa using hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      omega)
    -- The last leaf index is zero.
    have hu14' : digestValue val d / 2 ^ (26 + 10 * 14) % 2 ^ 10 = 0 := by
      obtain ⟨hlt, hbits, -⟩ := husv 14 (by omega)
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.zero_testBit]
      by_cases hi : i < 10
      · cases hb : (digestValue val d / 2 ^ (26 + 10 * 14) % 2 ^ 10).testBit i
        · rfl
        · have := (hbits i hi).mpr hb
          have hmem : (((List.range 15).map fun k => ((w0 ++ w1 ++ w2).drop (26 + 10 * k)).take 10).getD 14
              []).getD i 0 ∈ (((List.range 15).map fun k => ((w0 ++ w1 ++ w2).drop (26 + 10 * k)).take 10).getD 14
              []) := by
            have hl := huslen 14 (by omega)
            rw [List.getD_eq_getElem?_getD (l := ((List.range 15).map fun k =>
              ((w0 ++ w1 ++ w2).drop (26 + 10 * k)).take 10).getD 14 []), List.getElem?_eq_getElem (by omega)]
            exact List.getElem_mem _
          rw [limb_zero (hu14 st val (hsat.mono (by ext_chain)) _ hmem) 0] at this
          exact absurd this zero_ne_one
      · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega)))
    -- The message digest.
    have hzw : w64 val z = 0 := w64_const (hzv st val (hsat.mono (by ext_chain)))
    obtain ⟨hra, hrb, -, -⟩ := hrv st val (hsat.mono (by ext_chain))
    have hra' : val r0 0 = val rho 0 := hra
    have hrb' : val r1 0 = val rho 1 := hrb
    have hmd : Sphincs.Words.messageDigest (w64 val p0, w64 val p1) (w64 val rt0, w64 val rt1) (dig val rho)
        (w64 val m0, w64 val m1, w64 val m2, w64 val m3) =
        (digestValue val d % 2 ^ 26, fun κ => digestValue val d / 2 ^ (26 + 10 * κ) % 2 ^ 10) := by
      have hdd := hdv st val (hsat.mono (by ext_chain))
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, hzw,
        w64_of hra', w64_of hrb'] at hdd
      unfold Sphincs.Words.messageDigest
      simp only [tweak_eq, tw1, dig]
      rw [show BitVec.ofNat 64 (0 % 2 ^ 32 + 0 % 2 ^ 32 * 2 ^ 32) = 0 from rfl, ← hdd, words4_toNat, words4_toNat,
        words4_toNat]
      rfl
    -- The top layer's root is the statement's.
    have hroot : dig val msgF = (w64 val rt0, w64 val rt1) := by
      have e0 : val (rs.getD 0 0) 0 = val msgF 0 := hrsv st val (hsat.mono (by ext_chain)) 0
      have e1 : val (rs.getD 1 0) 0 = val msgF 1 := hrsv st val (hsat.mono (by ext_chain)) 1
      have u0 : val (rs.getD 0 0) = val ([rt0, rt1].getD 0 0) := hsat.unions _ (Ext.unions (by ext_chain) _ hu0)
      have u1 : val (rs.getD 1 0) = val ([rt0, rt1].getD 1 0) := hsat.unions _ hu1
      simp only [dig]
      rw [← w64_of e0, ← w64_of e1]
      simp only [w64, u0, u1]
      rfl
    refine ⟨(w64 val rt0, w64 val rt1), (w64 val p0, w64 val p1), (w64 val m0, w64 val m1, w64 val m2, w64 val m3),
      ⟨?_, ?_, ?_, ?_⟩, ⟨⟨dig val rho, fun κ => secrets κ, fun κ l => paths κ l, ctrs, fun j i => tipsF j i,
        fun j l => pathsF j l⟩, ?_⟩⟩
    · rw [hrtv st val (hsat.mono (by ext_chain))]; exact (limbs3_two _ _).symm
    · rw [← hst1, hpv st val (hsat.mono (by ext_chain))]; exact (limbs3_two _ _).symm
    · rw [show s.statement + 2 = s2.statement by omega, hmv1 st val (hsat.mono (by ext_chain))]
      exact (limbs3_two _ _).symm
    · rw [show s.statement + 3 = s3.statement by omega, hmv2 st val (hsat.mono (by ext_chain))]
      exact (limbs3_two _ _).symm
    · have hall := hfold ⟨dig val rho, fun κ => secrets κ, fun κ l => paths κ l, ctrs, fun j i => tipsF j i,
        fun j l => pathsF j l⟩ fun j _ => ⟨rfl, fun _ => rfl, fun _ _ => rfl⟩
      have hall' : ([2, 1, 0] : List (Fin 3)).foldlM (Sphincs.Words.layerRoot (w64 val p0, w64 val p1)
          (digestValue val d % 2 ^ 26) ⟨dig val rho, fun κ => secrets κ, fun κ l => paths κ l, ctrs,
            fun j i => tipsF j i, fun j l => pathsF j l⟩) (dig val msg0) = some (dig val msgF) := hall
      simp only [Sphincs.Words.verify, hmd, hu14', ne_eq, not_true_eq_false, if_false]
      rw [← hfts, hall', hroot]
      simp

/-- The circuit of `n ≤ 2^20` signatures: layer `lay` of signature `j` has 103 distinct `STEP` and 42 `LINK` rows,
`Rs g` and `Ls g` for its tag `g = 3 j + lay`, its rows under every satisfying assignment, and signature `j`'s
statement when its layers' tuples balance. -/
theorem circuit_good (n : ℕ) (hn : n ≤ 2 ^ 20) : Good (fun s => s.statement = 0) (Sphincs.Circuit.circuit n)
    fun _ _ s' => ∃ Rs Ls : ℕ → List (List ℕ), (∀ g < 3 * n, (Rs g).length = 103 ∧ (Ls g).length = 42 ∧
      (Rs g).Nodup ∧ (∀ r ∈ Rs g, r ∈ s'.step) ∧ ∀ r ∈ Ls g, r ∈ s'.link) ∧
    ∀ st val, Sat st s' val → (∀ g < 3 * n, SigRows g val (Rs g) (Ls g)) ∧ ∀ j < n,
      ((∀ lay < 3, LocalBal val (Rs (3 * j + lay)) (Ls (3 * j + lay))) →
        ∃ root pp msg, Encodes st j root pp msg ∧ ∃ sig, Sphincs.Words.verify root pp msg sig = true) := by
  unfold Sphincs.Circuit.circuit
  refine good_of_post fun s hs h0 => ?_
  refine post_bind (forIn_range_post n _ (fun k (_ : PUnit) s' => s'.statement = 4 * k ∧
      ∃ Rs Ls : ℕ → List (List ℕ), (∀ g < 3 * k, (Rs g).length = 103 ∧ (Ls g).length = 42 ∧ (Rs g).Nodup ∧
        (∀ r ∈ Rs g, r ∈ s'.step) ∧ ∀ r ∈ Ls g, r ∈ s'.link) ∧
      ∀ st val, Sat st s' val → (∀ g < 3 * k, SigRows g val (Rs g) (Ls g)) ∧ ∀ j < k,
        ((∀ lay < 3, LocalBal val (Rs (3 * j + lay)) (Ls (3 * j + lay))) →
          ∃ root pp msg, Encodes st j root pp msg ∧ ∃ sig, Sphincs.Words.verify root pp msg sig = true))
      hs ⟨by omega, fun _ => [], fun _ => [], fun g hg => absurd hg (by omega),
        fun _ _ _ => ⟨fun g hg => absurd hg (by omega), fun j hj => absurd hj (Nat.not_lt_zero j)⟩⟩ ?_) ?_
  · rintro k hk u s1 hi1 he1 ⟨hst1, Rs, Ls, hrows, hv1⟩
    refine (Sphincs.signature_good k (by omega)).step hi1 trivial ?_
    rintro _ s2 hi2 he2 ⟨hst2, RK, LK, hrowsK, hsig⟩
    refine post_pure hi2 he2 ⟨PUnit.unit, rfl, by omega, fun g => if g / 3 = k then RK (g % 3) else Rs g,
      fun g => if g / 3 = k then LK (g % 3) else Ls g, fun g hg => ?_, fun st val hsat => ?_⟩
    · by_cases hgk : g / 3 = k
      · simp only [if_pos hgk]
        exact hrowsK (g % 3) (Nat.mod_lt _ (by norm_num))
      · simp only [if_neg hgk]
        obtain ⟨h1, h2, h3, h4, h5⟩ := hrows g (by omega)
        exact ⟨h1, h2, h3, fun r hr => he2.steps _ (h4 r hr), fun r hr => he2.links _ (h5 r hr)⟩
    obtain ⟨hR1, hl1⟩ := hv1 st val (hsat.mono he2)
    obtain ⟨hRK, hlK⟩ := hsig st val hsat
    refine ⟨fun g hg => ?_, fun j hj hloc => ?_⟩
    · by_cases hgk : g / 3 = k
      · simp only [if_pos hgk]
        have := hRK (g % 3) (Nat.mod_lt _ (by norm_num))
        rwa [show 3 * k + g % 3 = g by omega] at this
      · simp only [if_neg hgk]
        exact hR1 g (by omega)
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hjk
      · refine hl1 j hj fun lay hlay => ?_
        have := hloc lay hlay
        simp only [if_neg (show ¬ (3 * j + lay) / 3 = k by omega)] at this
        exact this
      · obtain ⟨root, pp, msg, henc, hv⟩ := hlK fun lay hlay => by
          have := hloc lay hlay
          simp only [if_pos (show (3 * j + lay) / 3 = k by omega), show (3 * j + lay) % 3 = lay by omega] at this
          exact this
        rw [hst1, ← hjk] at henc
        exact ⟨root, pp, msg, henc, hv⟩
  · rintro u s1 hi1 he1 ⟨-, hv⟩
    exact post_pure hi1 he1 hv

/-- Soundness: in every assignment the machine accepts the circuit of `n ≤ 2^20` signatures with (its rows satisfied
and its dynamic bus balanced), statement words `4j .. 4j + 3` encode a root, a public parameter and a message for
which some signature verifies. The rows the signatures' layers name are all the circuit's (`count_circuit`,
`rows_perm`), so the balanced bus balances each layer's tuples (`local_of_balanced`). -/
theorem sound (n : ℕ) (hn : n ≤ 2 ^ 20) (st : ℕ → Fin 4 → K) (val : Val)
    (h : Accepts st ((Sphincs.Circuit.circuit n).run {}).2 val) :
    ∀ j < n, ∃ root pp msg, Encodes st j root pp msg ∧ ∃ sig, Sphincs.Words.verify root pp msg sig = true := by
  obtain ⟨hsat, hbal⟩ := h
  obtain ⟨Rs, Ls, hrows, hv⟩ := (Sphincs.circuit_good n hn {} inv_empty rfl).2.2
  obtain ⟨hfacts, hloc⟩ := hv st val hsat
  have hsize := Sphincs.count_circuit n {}
  simp only [Array.size_empty, Nat.zero_add] at hsize
  have hRnd := nodup_flatMap_label (3 * n) Rs (fun r => toWord (val (r.getD 4 0) 0) / 2 ^ 41)
    (fun g hg => (hrows g hg).2.2.1) fun g hg => (hfacts g hg).1
  have hLnd := nodup_flatMap_label (3 * n) Ls (fun r => toWord (val (r.getD 0 0) 0) / 2 ^ 41 % 2 ^ 22)
    (fun g hg => (hfacts g hg).2.1) fun g hg => (hfacts g hg).2.2.1
  have hR := rows_perm _ (3 * n) 103 Rs (by rw [hsize.1]; ring) (fun g hg => (hrows g hg).1)
    (fun g hg => (hrows g hg).2.2.2.1) hRnd
  have hL := rows_perm _ (3 * n) 42 Ls (by rw [hsize.2]; ring) (fun g hg => (hrows g hg).2.1)
    (fun g hg => (hrows g hg).2.2.2.2) hLnd
  have hb := local_of_balanced _ val (3 * n) Rs Ls hR hL hbal fun g hg => (hfacts g hg).2.2.2
  exact fun j hj => hloc j hj fun lay hlay => hb _ (by omega)

end LeanVMCircuits.Sphincs
