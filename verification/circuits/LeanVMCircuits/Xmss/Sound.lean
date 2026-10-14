module

public import LeanVMCircuits.Xmss.SoundGadgets
public import LeanVMCircuits.Xmss.Statement

@[expose] public section

/-!
# Soundness of the leanXMSS circuit

In every assignment the machine accepts the circuit of `n ≤ 2^22` signatures with (`Accepts`: its rows satisfied and
its dynamic bus balanced), statement words `5j .. 5j + 4` encode a public parameter, a root, a message and an epoch
below `2^32` for which some signature verifies over words (`Words.verify`). The signature is read off the
assignment: the links' chain elements, the randomness and the siblings are the circuit's free wires.

Per signature (`signature_good`): the statement words decode by the `CAST` rows' views and the zeros held to their
top words; the epoch's bits are its split's, the top 32 held zero; the encoding's digest is its hash row chain's,
its digits the splits of its first two words, which sum to 195 because their product reaches `x^195`; the path
climbs on the epoch's bits to the exposed root. Its chains (`chains_local`) are `Paths.local_sound` on its `STEP`
and `LINK` rows, whose tuples all carry keys of signature `j`. For the whole circuit (`sound`), the rows the
signatures name are all the circuit's rows (`count_circuit`, `rows_perm`), so the balanced bus balances each
signature's tuples (`local_of_balanced`).
-/

namespace LeanVMCircuits.Xmss

open LeanVMCircuits.Rec (K E toE emb ofWord toWord words4 digest hashWords num root toE_injective tweakWord tweakK
  dynKey)
open LeanVMCircuits.Rec.Model
open Words (W Dig)

/-- One signature's statement words from statement word `b` on. -/
def EncodesAt (st : ℕ → Fin 4 → K) (b : ℕ) (pp root : Dig) (msg : W × W × W × W) (epoch : ℕ) : Prop :=
  epoch < 2 ^ 32 ∧ st b = limbs3 pp.1 pp.2 0 ∧ st (b + 1) = limbs3 msg.1 msg.2.1 0 ∧
  st (b + 2) = limbs3 msg.2.2.1 msg.2.2.2 0 ∧ st (b + 3) = limbs3 (BitVec.ofNat 64 epoch) 0 0 ∧
  st (b + 4) = limbs3 root.1 root.2 0

theorem ofWord_ofNat_toWord (z : K) : ofWord (BitVec.ofNat 64 (toWord z)).toNat = z := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (toWord_lt z), ofWord_toWord]

theorem ofWord_zeroW : ofWord (0 : W).toNat = 0 := by
  rw [show (0 : W).toNat = 0 from rfl]; exact Rec.ofWord_zero

theorem limbs3_two (x y : K) :
    limbs3 (BitVec.ofNat 64 (toWord x)) (BitVec.ofNat 64 (toWord y)) 0 = ![x, y, 0, 0] := by
  simp only [limbs3, ofWord_ofNat_toWord, ofWord_zeroW]

theorem limbs3_one (x : K) : limbs3 (BitVec.ofNat 64 (toWord x)) 0 0 = ![x, 0, 0, 0] := by
  simp only [limbs3, ofWord_ofNat_toWord, ofWord_zeroW]

/-! Lists. -/

theorem flatMap_range_congr {f g : ℕ → List W} {n : ℕ} (h : ∀ j < n, f j = g j) :
    (List.range n).flatMap f = (List.range n).flatMap g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih fun j hj => h j (by omega)]
    simp only [List.flatMap_cons, List.flatMap_nil, h n (by omega)]

theorem foldl_range_congr {α : Type} {f g : α → ℕ → α} {n : ℕ} {x : α} (h : ∀ c, ∀ j < n, f c j = g c j) :
    (List.range n).foldl f x = (List.range n).foldl g x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, ih fun c j hj => h c j (by omega)]
    simp only [List.foldl_cons, List.foldl_nil, h _ n (by omega)]

theorem ofFn_flatMap (F : ℕ → Dig) :
    (List.ofFn fun i : Fin 42 => F i.val).flatMap (fun d => [d.1, d.2]) =
      (List.range 42).flatMap fun i => [(F i).1, (F i).2] := by
  have : (List.ofFn fun i : Fin 42 => F i.val) = (List.range 42).map F := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_map, List.length_range]
    · intro i h1 h2
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  rw [this, List.flatMap_map]

theorem climb_eq (e : ℕ) (P : Dig) (path : ℕ → Dig) (leaf : Dig) :
    Words.climb e P (fun l => path l.val) leaf =
      (List.range 32).foldl (fun c l => Words.parent e l P c (path l)) leaf := by
  unfold Words.climb
  have : (List.finRange 32).map Fin.val = List.range 32 := by
    apply List.ext_getElem <;> simp
  rw [← this, List.foldl_map]

theorem digitBits_getD (lo up : List ℕ) (hlo : lo.length = 64) (j : ℕ) (hj : j < 126) :
    (lo.take 63 ++ up.take 63).getD j 0 = if j < 63 then lo.getD j 0 else up.getD (j - 63) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append, List.length_take, hlo,
    show min 63 64 = 63 from rfl]
  by_cases h : j < 63
  · rw [if_pos h, if_pos h, List.getElem?_take_of_lt h, List.getD_eq_getElem?_getD]
  · rw [if_neg h, if_neg h, List.getElem?_take_of_lt (show j - 63 < 63 by omega), List.getD_eq_getElem?_getD]

/-! Digits. -/

/-- A digit of a word given by its bits. -/
theorem digit_bits (w : W) (r : ℕ) (hr : 3 * r + 2 < 64) (val : Val) (bs : List ℕ)
    (h : ∀ j < 64, (w.toNat.testBit j = true ↔ val (bs.getD j 0) 0 = 1)) :
    Words.digit w r = dig3 val (bs.getD (3 * r) 0) (bs.getD (3 * r + 1) 0) (bs.getD (3 * r + 2) 0) := by
  unfold Words.digit dig3
  have hb : ∀ k < 3, (w.toNat / 2 ^ (3 * r) / 2 ^ k % 2 = 1 ↔ val (bs.getD (3 * r + k) 0) 0 = 1) := by
    intro k hk
    rw [← h (3 * r + k) (by omega), Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff, Nat.div_div_eq_div_mul,
      ← pow_add]
  generalize w.toNat / 2 ^ (3 * r) = n at hb ⊢
  have e0 := hb 0 (by norm_num)
  have e1 := hb 1 (by norm_num)
  have e2 := hb 2 (by norm_num)
  simp only [pow_zero, Nat.div_one, pow_one, Nat.add_zero] at e0 e1 e2
  have f0 : n % 2 = if val (bs.getD (3 * r) 0) 0 = 1 then 1 else 0 := by
    split_ifs with hc
    · exact e0.mpr hc
    · have := mt e0.mp hc; omega
  have f1 : n / 2 % 2 = if val (bs.getD (3 * r + 1) 0) 0 = 1 then 1 else 0 := by
    split_ifs with hc
    · exact e1.mpr hc
    · have := mt e1.mp hc; omega
  have f2 : n / 2 ^ 2 % 2 = if val (bs.getD (3 * r + 2) 0) 0 = 1 then 1 else 0 := by
    split_ifs with hc
    · exact e2.mpr hc
    · have := mt e2.mp hc; omega
  have key : n % 8 = n % 2 + 2 * (n / 2 % 2) + 4 * (n / 2 ^ 2 % 2) := by
    rw [show (2 : ℕ) ^ 2 = 4 from rfl]; omega
  rw [key, f0, f1, f2]
  split_ifs <;> omega

theorem digits_getD (D : Dig) (j : ℕ) (hj : j < 42) :
    (Words.digits D).getD j 0 = Words.digit (if j < 21 then D.1 else D.2) (j % 21) := by
  simp [Words.digits, List.getD_eq_getElem?_getD, hj]

/-- Digit `i` of the encoding is the value of its digit bits. -/
theorem digit_dval (val : Val) (d : ℕ) (lo up : List ℕ) (hlo : lo.length = 64)
    (hlo' : ∀ j < 64, ((dig val d).1.toNat.testBit j = true ↔ val (lo.getD j 0) 0 = 1))
    (hup' : ∀ j < 64, ((dig val d).2.toNat.testBit j = true ↔ val (up.getD j 0) 0 = 1)) (i : ℕ) (hi : i < 42) :
    Words.digit (if i < 21 then (dig val d).1 else (dig val d).2) (i % 21) = dval val (lo.take 63 ++ up.take 63) i := by
  unfold dval
  rw [digitBits_getD _ _ hlo (3 * i) (by omega), digitBits_getD _ _ hlo (3 * i + 1) (by omega),
    digitBits_getD _ _ hlo (3 * i + 2) (by omega)]
  by_cases h21 : i < 21
  · rw [if_pos h21, Nat.mod_eq_of_lt h21, digit_bits _ i (by omega) val lo hlo', if_pos (show 3 * i < 63 by omega),
      if_pos (show 3 * i + 1 < 63 by omega), if_pos (show 3 * i + 2 < 63 by omega)]
  · rw [if_neg h21, digit_bits _ (i % 21) (by omega) val up hup', if_neg (show ¬ 3 * i < 63 by omega),
      if_neg (show ¬ 3 * i + 1 < 63 by omega), if_neg (show ¬ 3 * i + 2 < 63 by omega),
      show 3 * i - 63 = 3 * (i % 21) by omega, show 3 * i + 1 - 63 = 3 * (i % 21) + 1 by omega,
      show 3 * i + 2 - 63 = 3 * (i % 21) + 2 by omega]

/-- The encoding's digits sum to the digit bits' values. -/
theorem digits_sum (val : Val) (d : ℕ) (lo up : List ℕ) (hlo : lo.length = 64)
    (hlo' : ∀ j < 64, ((dig val d).1.toNat.testBit j = true ↔ val (lo.getD j 0) 0 = 1))
    (hup' : ∀ j < 64, ((dig val d).2.toNat.testBit j = true ↔ val (up.getD j 0) 0 = 1)) :
    (Words.digits (dig val d)).sum = dsum val (lo.take 63 ++ up.take 63) 42 := by
  unfold Words.digits dsum
  rw [List.map_congr_left fun i hi => digit_dval val d lo up hlo hlo' hup' i (List.mem_range.mp hi)]

/-! Wire lists. -/

theorem wires_append_take {lo up : List ℕ} {s : State} (hlo : Wires lo s) (hup : Wires up s) :
    Wires (lo.take 63 ++ up.take 63) s := fun w hw =>
  (List.mem_append.mp hw).elim (fun h => hlo w (List.mem_of_mem_take h)) (fun h => hup w (List.mem_of_mem_take h))

theorem getD_mem_drop {bits : List ℕ} (hlen : bits.length = 64) {i : ℕ} (h1 : 32 ≤ i) (h2 : i < 64) :
    bits.getD i 0 ∈ bits.drop 32 := by
  have h : (bits.drop 32)[i - 32]? = some (bits.getD i 0) := by
    rw [List.getElem?_drop, show 32 + (i - 32) = i by omega, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  exact List.mem_iff_getElem?.mpr ⟨_, h⟩

/-! The chains. -/

/-- Tag `g`'s rows under an assignment: its `STEP` rows carry the tag `g · 2^41`, its `LINK` rows are distinct and
carry tag `g`'s words, and every tuple they push or pull has a key of tag `g`. -/
def SigRows (g : ℕ) (val : Val) (R L : List (List ℕ)) : Prop :=
  (∀ r ∈ R, toWord (val (r.getD 4 0) 0) / 2 ^ 41 = g) ∧ L.Nodup ∧
    (∀ r ∈ L, toWord (val (r.getD 0 0) 0) / 2 ^ 41 % 2 ^ 22 = g) ∧
    ∀ t ∈ (R.map (stepPushRow val) ++ L.map (linkPushRow val)) ++
      (R.map (stepPullRow val) ++ L.map (linkPullRow val)), tagOf t.1 = g

/-- Chains of tag `g` over the base `b` under an assignment satisfying their rows: their rows are tag `g`'s, and when
their tuples balance (and the steps and the digits sum to 294) the links' ends are the chains' ends from their
elements, walked by `stepHash`. -/
theorem chains_local {b g steps idx p0 p1 : ℕ} {db : List ℕ} {R : List (List ℕ)} {act tag : ℕ}
    {W T0 T1 E0 E1 : ℕ → ℕ} {s : State} {st : ℕ → Fin 4 → K} {val : Val} (hsat : Sat st s val) (hb : b < 2 ^ 32)
    (hg : g < 2 ^ 22) (hR : ∀ r ∈ R, StepRow idx p0 p1 b tag act s r) (hRl : R.length = steps)
    (hact : val act 0 = 1) (htag : val tag 0 = ofWord (g * 2 ^ 41))
    (hW : ∀ i < 42, val (W i) 0 = ofWord (tweakWord b (8 * i) + g * 2 ^ 41))
    (hdb : ∀ k < 126, val (db.getD k 0) 0 = 0 ∨ val (db.getD k 0) 0 = 1) :
    SigRows g val R ((List.range 42).map (linkRow db act W T0 T1 E0 E1)) ∧
      (steps + dsum val db 42 = 294 → LocalBal val R ((List.range 42).map (linkRow db act W T0 T1 E0 E1)) →
        ((List.range 42).flatMap fun i => [E0 i, E1 i]).map (w64 val) = (List.range 42).flatMap fun i =>
          [(walk (stepHash b (w64 val idx) (w64 val p0) (w64 val p1)) i (dval val db i)
              (w64 val (T0 i), w64 val (T1 i)) 7).1,
            (walk (stepHash b (w64 val idx) (w64 val p0) (w64 val p1)) i (dval val db i)
              (w64 val (T0 i), w64 val (T1 i)) 7).2]) := by
  -- Each step: its position, its keys, its hash.
  have hstep : ∀ r ∈ R, ∃ p < 2 ^ 9, val (r.getD 0 0) 0 = tweakK (ofWord b) p ∧
      (stepPullRow val r).1 = keyK b g p ∧ (stepPushRow val r).1 = keyK b g (8 * (p / 8) + (p % 8 + 1) % 8) ∧
      wd (stepPushRow val r) =
        stepHash b (w64 val idx) (w64 val p0) (w64 val p1) (p / 8) (p % 8) (wd (stepPullRow val r)) := by
    intro r hr
    obtain ⟨t, v0, v1, ch, base, rfl, -, -, hq⟩ := hR r hr
    obtain ⟨hh, c, hc, i, hi, hT, hpush⟩ := hq st val hsat
    have hpd : (8 * c + i) / 8 = c := by omega
    have hpm : (8 * c + i) % 8 = i := by omega
    refine ⟨8 * c + i, by omega, hT, ?_, ?_, ?_⟩
    · show dynKey (val t 0) (val tag 0) = _
      rw [hT, htag, keyK_def]
    · rw [hpush hact, hpd, hpm, keyK_def]
      show dynKey _ (val tag 0) = _
      rw [htag]
    · rw [hpush hact, hpd, hpm]
      show (words4 (val ch) 0, words4 (val ch) 1) =
        stepHash b (w64 val idx) (w64 val p0) (w64 val p1) c i (w64 val v0, w64 val v1)
      have ht : w64 val t = BitVec.ofNat 64 (tweakWord b (8 * c + i)) := by
        rw [w64, hT, ← Rec.ofWord_tweakWord _ _ hb (by omega), Rec.toWord_ofWord _ (by unfold tweakWord; omega)]
      have hmap : [t, idx, p0, p1, v0, v1].map (w64 val) =
          [BitVec.ofNat 64 (tweakWord b (8 * c + i)), w64 val idx, w64 val p0, w64 val p1, w64 val v0, w64 val v1] := by
        simp only [List.map_cons, List.map_nil, ht]
      rw [hh 0 (by decide), hh 1 (by decide), hmap]
      simp only [stepHash]
  -- Each link: its keys.
  have hlpush : ∀ i < 42, (linkPushRow val (linkRow db act W T0 T1 E0 E1 i)).1 = keyK b g (8 * i + dval val db i) := by
    intro i hi
    show dynKey (val (W i) 0) (ofWord (2 ^ 32) * val (db.getD (3 * i) 0) 0 +
      ofWord (2 ^ 33) * val (db.getD (3 * i + 1) 0) 0 + ofWord (2 ^ 34) * val (db.getD (3 * i + 2) 0) 0) = _
    rw [hW i hi, link_push_key b i g hb hi hg _ _ _ (hdb _ (by omega)) (hdb _ (by omega)) (hdb _ (by omega))]
    rfl
  have hlpull : ∀ i < 42, (linkPullRow val (linkRow db act W T0 T1 E0 E1 i)).1 = keyK b g (8 * i + 7) := by
    intro i hi
    show dynKey (val (W i) 0) (ofWord (2 ^ 32 + 2 ^ 33 + 2 ^ 34) * val act 0) = _
    rw [hW i hi, hact]
    exact link_pull_key b i g hb hi hg
  refine ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_, fun t ht => ?_⟩, fun hsum hloc => ?_⟩
  · obtain ⟨t, v0, v1, ch, base, rfl, -⟩ := hR r hr
    show toWord (val tag 0) / 2 ^ 41 = g
    rw [htag, Rec.toWord_ofWord _ (by omega)]
    omega
  · refine List.Nodup.map_on (fun x hx y hy hxy => ?_) List.nodup_range
    have hx' := List.mem_range.mp hx
    have hy' := List.mem_range.mp hy
    have h0 : val (W x) 0 = val (W y) 0 := by rw [show W x = W y from (List.cons.inj hxy).1]
    rw [hW x hx', hW y hy'] at h0
    have h1 := congrArg toWord h0
    rw [toWord_link b x g hb hx' hg, toWord_link b y g hb hy' hg] at h1
    omega
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    show toWord (val (W i) 0) / 2 ^ 41 % 2 ^ 22 = g
    rw [hW i (List.mem_range.mp hi), toWord_link b i g hb (List.mem_range.mp hi) hg]
    have := List.mem_range.mp hi
    omega
  · simp only [List.mem_append, List.map_map, List.mem_map, Function.comp] at ht
    rcases ht with (⟨r, hr, rfl⟩ | ⟨i, hi, rfl⟩) | (⟨r, hr, rfl⟩ | ⟨i, hi, rfl⟩)
    · obtain ⟨p, hp, -, -, hpush, -⟩ := hstep r hr
      rw [hpush, tagOf_keyK _ _ _ hb (by omega) hg]
    · have hi' := List.mem_range.mp hi
      have := dval_lt val db i
      rw [hlpush i hi', tagOf_keyK _ _ _ hb (by omega) hg]
    · obtain ⟨p, hp, -, hpull, -, -⟩ := hstep r hr
      rw [hpull, tagOf_keyK _ _ _ hb hp hg]
    · have hi' := List.mem_range.mp hi
      rw [hlpull i hi', tagOf_keyK _ _ _ hb (by omega) hg]
  -- The chains' ends.
  have hres := local_sound (stepHash b (w64 val idx) (w64 val p0) (w64 val p1)) b g hb hg val R
    (fun r => posOf (val (r.getD 0 0) 0)) (linkRow db act W T0 T1 E0 E1) (dval val db)
    (fun r hr => by obtain ⟨p, hp, hT, -⟩ := hstep r hr; rw [hT, posOf_tweak b p hb hp]; exact hp)
    (fun r hr => by obtain ⟨p, hp, hT, h1, -⟩ := hstep r hr; rw [hT, posOf_tweak b p hb hp]; exact h1)
    (fun r hr => by obtain ⟨p, hp, hT, -, h2, -⟩ := hstep r hr; rw [hT, posOf_tweak b p hb hp]; exact h2)
    (fun r hr => by obtain ⟨p, hp, hT, -, -, h3⟩ := hstep r hr; rw [hT, posOf_tweak b p hb hp]; exact h3)
    (fun i _ => dval_lt val db i) hlpush hlpull
    (by rw [hRl, ← sum_range_list]; unfold dsum at hsum; exact hsum) hloc
  rw [List.map_flatMap]
  refine flatMap_range_eq fun i hi => ?_
  have h : (w64 val (E0 i), w64 val (E1 i)) = walk (stepHash b (w64 val idx) (w64 val p0) (w64 val p1)) i
      (dval val db i) (w64 val (T0 i), w64 val (T1 i)) 7 := hres i hi
  simp only [List.map_cons, List.map_nil]
  rw [← h]

/-! One signature. -/

theorem signature_good (j : ℕ) (hj : j < 2 ^ 22) : Good (fun _ => True) (Circuit.signature j) fun s _ s' =>
    s'.statement = s.statement + 5 ∧ ∃ R L : List (List ℕ), R.length = 99 ∧ L.length = 42 ∧ R.Nodup ∧
      (∀ r ∈ R, r ∈ s'.step) ∧ (∀ r ∈ L, r ∈ s'.link) ∧ ∀ st val, Sat st s' val → SigRows j val R L ∧
        (LocalBal val R L → ∃ pp root msg epoch, EncodesAt st s.statement pp root msg epoch ∧
          ∃ sig, Words.verify pp root msg epoch sig = true) := by
  unfold Circuit.signature
  refine good_of_post fun s hs _ => ?_
  refine statementWords_good1.step hs trivial ?_
  rintro _ s1 hi1 he1 ⟨hst1, p0, p1, rfl, hp0, hp1, hpv⟩
  refine statementWords_good1.step hi1 trivial ?_
  rintro _ s2 hi2 he2 ⟨hst2, m0, m1, rfl, hm0, hm1, hmv1⟩
  refine statementWords_good1.step hi2 trivial ?_
  rintro _ s3 hi3 he3 ⟨hst3, m2, m3, rfl, hm2, hm3, hmv2⟩
  refine statementWords_good2.step hi3 trivial ?_
  rintro _ s4 hi4 he4 ⟨hst4, e0, rfl, he0, hev⟩
  refine ((kConst_good 0).pres (pres_kConst 0)).step hi4 trivial ?_
  rintro z s5 hi5 he5 ⟨hst5, hz, hzv⟩
  refine ((split_good _).pres (pres_split _)).step hi5 trivial ?_
  rintro bits s6 hi6 he6 ⟨hst6, hblen, hbw, hbv⟩
  refine (zeros_good _).step hi6 trivial ?_
  rintro _ s7 hi7 he7 ⟨hst7, hbz⟩
  refine (indexWord_good bits 0 (by omega) (by omega)).step hi7 (hbw.mono he7) ?_
  rintro idx s8 hi8 he8 ⟨hst8, hidx, hidxv⟩
  refine fresh_good'.step hi8 trivial ?_
  rintro rho s9 hi9 he9 ⟨hst9, hrho⟩
  refine (words_good rho).step hi9 (Wires.cons' hrho Wires.nil') ?_
  rintro ⟨r0, r1, r2⟩ s10 hi10 he10 ⟨hst10, hr0, hr1, hr2, hrv⟩
  try dsimp only
  refine (tweakHash_good 4 0 idx [p0, p1] ([m0, m1] ++ [m2, m3] ++ [r0, r1, r2, z]) (by norm_num)).step hi10
    trivial ?_
  rintro d s11 hi11 he11 ⟨hst11, hd, hdv⟩
  refine ((dToK_good d).pres (pres_dToK d)).step hi11 (Wires.cons' hd Wires.nil') ?_
  rintro ks s12 hi12 he12 ⟨hst12, hks, hksv⟩
  refine ((split_good _).pres (pres_split _)).step hi12 trivial ?_
  rintro lo s13 hi13 he13 ⟨hst13, hlolen, hlow, hlov⟩
  refine ((split_good _).pres (pres_split _)).step hi13 trivial ?_
  rintro up s14 hi14 he14 ⟨hst14, huplen, hupw, hupv⟩
  refine ((eqConstK_good _ 0).pres (pres_eqConstK _ 0)).step hi14 trivial ?_
  rintro _ s15 hi15 he15 ⟨hst15, hlo63⟩
  refine ((eqConstK_good _ 0).pres (pres_eqConstK _ 0)).step hi15 trivial ?_
  rintro _ s16 hi16 he16 ⟨hst16, hup63⟩
  have hDBw : Wires (lo.take 63 ++ up.take 63) s16 :=
    wires_append_take (hlow.mono (by ext_chain)) (hupw.mono (by ext_chain))
  have hDBlen : (lo.take 63 ++ up.take 63).length = 126 := by simp [hlolen, huplen]
  refine (digitProduct_good _ (by omega)).step hi16 hDBw ?_
  rintro prod s17 hi17 he17 ⟨hst17, hprod, hprodv⟩
  refine ((eqConstE_good prod Circuit.targetWord 0 0).pres (pres_eqConstE _ _ _ _)).step hi17 trivial ?_
  rintro _ s18 hi18 he18 ⟨hst18, htarget⟩
  -- What every later assignment says of the epoch, its bits and the digit bits.
  have hctx : ∀ st val, Sat st s18 val →
      (∀ j < 64, (val (bits.getD j 0) 0 = 1 ↔ (toWord (val e0 0)).testBit j = true)) ∧
      toWord (val e0 0) < 2 ^ 32 ∧ (∀ j < 64, val (bits.getD j 0) 0 = 0 ∨ val (bits.getD j 0) 0 = 1) ∧
      w64 val idx = Words.tweak1 (toWord (val e0 0)) ∧
      (∀ j < 126, val ((lo.take 63 ++ up.take 63).getD j 0) 0 = 0 ∨
        val ((lo.take 63 ++ up.take 63).getD j 0) 0 = 1) := by
    intro st val hsat
    obtain ⟨hbool, hnum⟩ := hbv st val (hsat.mono (by ext_chain))
    have hnum' : toWord (val e0 0) = num (fun i => if val (bits.getD i 0) 0 = 1 then 1 else 0) 64 := hnum
    have hbits : ∀ j < 64, (val (bits.getD j 0) 0 = 1 ↔ (toWord (val e0 0)).testBit j = true) :=
      fun j hj => (testBit_split hnum' j hj).symm
    have hlt : toWord (val e0 0) < 2 ^ 32 := by
      apply Nat.lt_pow_two_of_testBit
      intro i hi
      by_cases h64 : i < 64
      · have h0 : val (bits.getD i 0) 0 = 0 :=
          limb_zero (hbz st val (hsat.mono (by ext_chain)) _ (getD_mem_drop hblen hi h64)) 0
        cases hb : (toWord (val e0 0)).testBit i
        · rfl
        · have := (hbits i h64).mpr hb; rw [h0] at this; exact absurd this zero_ne_one
      · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (toWord_lt _) (Nat.pow_le_pow_right (by norm_num) (by omega)))
    refine ⟨hbits, hlt, hbool, ?_, fun j hj => ?_⟩
    · have := hidxv st val (hsat.mono (by ext_chain)) _ hlt fun i hi => hbits i (by omega)
      rwa [pow_zero, Nat.div_one] at this
    · rw [digitBits_getD _ _ hlolen j hj]
      split_ifs with h
      · exact (hlov st val (hsat.mono (by ext_chain))).1 j (by omega)
      · exact (hupv st val (hsat.mono (by ext_chain))).1 (j - 63) (by omega)
  -- The chains.
  refine (chains_good (2 ^ 8) j 99 idx p0 p1 (lo.take 63 ++ up.take 63)).step hi18 trivial ?_
  · rintro ends s19 hi19 he19 ⟨hst19, hw19, R, act, tag, W, T0, T1, E0, E1, rfl, hRl, hRn, hR, hL, hv19⟩
    refine (tweakHash_good 2 0 idx [p0, p1] _ (by rw [List.length_flatMap]; simp)).step hi19
      trivial ?_
    rintro node0 s20 hi20 he20 ⟨hst20, hnode0, hnode0v⟩
    -- The path.
    refine post_bind (forIn_range_post 32 _ (fun k (node : ℕ) s' => s'.statement = s.statement + 4 ∧
        node < s'.next ∧ ∀ st val, Sat st s' val → ∃ path : ℕ → Dig,
          dig val node = (List.range k).foldl (fun c l => Words.parent (toWord (val e0 0)) l
            (w64 val p0, w64 val p1) c (path l)) (dig val node0)) hi20
        ⟨by omega, hnode0, fun _ _ _ => ⟨fun _ => (0, 0), rfl⟩⟩ ?_) ?_
    · rintro l hl node s21 hi21 he21 ⟨hst21, hnode, hv21⟩
      refine (indexWord_good bits (l + 1) (by omega) (by omega)).step hi21 (hbw.mono (by ext_chain)) ?_
      rintro ix s22 hi22 he22 ⟨hst22, hix, hixv⟩
      refine (level_good l ix (bits.getD l 0) node p0 p1).step hi22 ⟨hix,
        lt_mono (wires_getD' hbw (by omega)) (by ext_chain), lt_mono hnode he22, lt_mono hp0 (by ext_chain),
        lt_mono hp1 (by ext_chain)⟩ ?_
      rintro node' s23 hi23 he23 ⟨hst23, hnode', hv23⟩
      refine post_pure hi23 (by ext_chain) ⟨node', rfl, by omega, hnode', fun st val hsat => ?_⟩
      obtain ⟨hbits, hlt, hbool, -, -⟩ := hctx st val (hsat.mono (by ext_chain))
      obtain ⟨path, hpath⟩ := hv21 st val (hsat.mono (by ext_chain))
      obtain ⟨sib, hsib⟩ := hv23 st val hsat
      have hixe := hixv st val (hsat.mono he23) _ hlt fun i hi => hbits i (by omega)
      have hstep := hsib _ hixe (hbool l (by omega)) (hbits l (by omega))
      refine ⟨fun j => if j = l then sib else path j, ?_⟩
      rw [hstep, hpath, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      beta_reduce
      rw [if_pos rfl, foldl_range_congr (g := fun c j => Words.parent (toWord (val e0 0)) j (w64 val p0, w64 val p1) c
          (if j = l then sib else path j)) fun c j hj => by rw [if_neg (show ¬ j = l by omega)]]
    · rintro node s21 hi21 he21 ⟨hst21, hnode, hv21⟩
      refine ((dToK_good node).pres (pres_dToK node)).step hi21 (Wires.cons' hnode Wires.nil') ?_
      rintro rs s22 hi22 he22 ⟨hst22, hrs, hrsv⟩
      refine (kToE_good' _ _ _).step hi22 (Wires.cons' (hrs 0 (by omega))
        (Wires.cons' (hrs 1 (by omega)) (Wires.cons' (lt_mono hz (by ext_chain)) Wires.nil'))) ?_
      rintro root s23 hi23 he23 ⟨hst23, hroot, hrootv⟩
      refine (expose_good' root).step hi23 (Wires.cons' hroot Wires.nil') ?_
      rintro _ s24 hi24 he24 ⟨rfl, hst24, hx⟩
      refine post_pure hi24 (by ext_chain) ⟨by omega, R, (List.range 42).map
        (linkRow (lo.take 63 ++ up.take 63) act W T0 T1 E0 E1), hRl, by simp, hRn, fun r hr => ?_,
        fun r hr => ?_, fun st val hsat => ?_⟩
      · obtain ⟨_, _, _, _, _, -, hmem, -⟩ := hR r hr
        exact (show Ext s19 s24 by ext_chain).steps _ hmem
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
        exact (show Ext s19 s24 by ext_chain).links _ (hL i (List.mem_range.mp hi))
      -- Read everything off the final assignment.
      obtain ⟨hbits, hlt, hbool, hidxe, hDB⟩ := hctx st val (hsat.mono (by ext_chain))
      have hsat19 := hsat.mono (show Ext s19 s24 by ext_chain)
      obtain ⟨hact, htag, hW⟩ := hv19 st val hsat19
      obtain ⟨hrows, hlocal⟩ := chains_local hsat19 (by norm_num) hj hR hRl hact htag hW hDB
      refine ⟨hrows, fun hloc => ?_⟩
      obtain ⟨path, hpath⟩ := hv21 st val (hsat.mono (by ext_chain))
      -- The encoding's digest and digits.
      have hzw : w64 val z = 0 := w64_const (hzv st val (hsat.mono (by ext_chain)))
      have hD : dig val d = Words.th 4 0 (toWord (val e0 0)) (w64 val p0, w64 val p1)
          [w64 val m0, w64 val m1, w64 val m2, w64 val m3, w64 val r0, w64 val r1, w64 val r2, 0] := by
        apply dig_th
        rw [hdv st val (hsat.mono (by ext_chain)), hidxe]
        simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, hzw]
      have hks0 : val (ks.getD 0 0) 0 = val d 0 := hksv st val (hsat.mono (by ext_chain)) 0
      have hks1 : val (ks.getD 1 0) 0 = val d 1 := hksv st val (hsat.mono (by ext_chain)) 1
      have hlonum : toWord (val d 0) = num (fun i => if val (lo.getD i 0) 0 = 1 then 1 else 0) 64 := by
        rw [← hks0]; exact (hlov st val (hsat.mono (by ext_chain))).2
      have hupnum : toWord (val d 1) = num (fun i => if val (up.getD i 0) 0 = 1 then 1 else 0) 64 := by
        rw [← hks1]; exact (hupv st val (hsat.mono (by ext_chain))).2
      have hlo' : ∀ j < 64, ((dig val d).1.toNat.testBit j = true ↔ val (lo.getD j 0) 0 = 1) := by
        intro j hj
        rw [show (dig val d).1 = words4 (val d) 0 from rfl, words4_toNat]
        exact testBit_split hlonum j hj
      have hup' : ∀ j < 64, ((dig val d).2.toNat.testBit j = true ↔ val (up.getD j 0) 0 = 1) := by
        intro j hj
        rw [show (dig val d).2 = words4 (val d) 1 from rfl, words4_toNat]
        exact testBit_split hupnum j hj
      have hsum : (Words.digits (dig val d)).sum = 195 := by
        rw [digits_sum val d lo up hlolen hlo' hup']
        apply eq_195 _ (le_trans (dsum_le _ _ 42) (by norm_num))
        apply emb_injective
        rw [← hprodv st val (hsat.mono (by ext_chain)) hDB, htarget st val (hsat.mono (by ext_chain)),
          Rec.ofWord_zero, toE_emb, target_eq]
      have hsum' : dsum val (lo.take 63 ++ up.take 63) 42 = 195 := by
        rw [← digits_sum val d lo up hlolen hlo' hup']; exact hsum
      obtain ⟨tips, htips⟩ : ∃ tips : ℕ → Dig, ((List.range 42).flatMap fun i => [E0 i, E1 i]).map (w64 val) =
          (List.range 42).flatMap fun i =>
            [(Words.chainFrom i (toWord (val e0 0)) (w64 val p0, w64 val p1) (dval val (lo.take 63 ++ up.take 63) i)
              (tips i)).1,
             (Words.chainFrom i (toWord (val e0 0)) (w64 val p0, w64 val p1) (dval val (lo.take 63 ++ up.take 63) i)
              (tips i)).2] :=
        ⟨fun i => (w64 val (T0 i), w64 val (T1 i)), by
          rw [hlocal (by rw [hsum']) hloc, hidxe]
          simp only [walk_stepHash]⟩
      have h63lo : (dig val d).1.getLsbD 63 = false := by
        cases hb : (dig val d).1.getLsbD 63
        · rfl
        · have := (hlo' 63 (by omega)).mp hb
          rw [limb_zero (hlo63 st val (hsat.mono (by ext_chain))) 0] at this
          exact absurd this zero_ne_one
      have h63up : (dig val d).2.getLsbD 63 = false := by
        cases hb : (dig val d).2.getLsbD 63
        · rfl
        · have := (hup' 63 (by omega)).mp hb
          rw [limb_zero (hup63 st val (hsat.mono (by ext_chain))) 0] at this
          exact absurd this zero_ne_one
      have henc : Words.encode (w64 val p0, w64 val p1) (w64 val m0, w64 val m1, w64 val m2, w64 val m3)
          (w64 val r0, w64 val r1, w64 val r2) (toWord (val e0 0)) = some (Words.digits (dig val d)) := by
        simp only [Words.encode, ← hD, h63lo, h63up, hsum, and_self, if_true]
      -- The leaf.
      have hdig : ∀ j < 42, (Words.digits (dig val d)).getD j 0 = dval val (lo.take 63 ++ up.take 63) j :=
        fun j hj => by rw [digits_getD _ j hj, digit_dval val d lo up hlolen hlo' hup' j hj]
      have hF := ofFn_flatMap (fun j => Words.chainFrom j (toWord (val e0 0)) (w64 val p0, w64 val p1)
        ((Words.digits (dig val d)).getD j 0) (tips j))
      beta_reduce at hF
      have hcong : ((List.range 42).flatMap fun i =>
          [(Words.chainFrom i (toWord (val e0 0)) (w64 val p0, w64 val p1) (dval val (lo.take 63 ++ up.take 63) i)
            (tips i)).1,
           (Words.chainFrom i (toWord (val e0 0)) (w64 val p0, w64 val p1) (dval val (lo.take 63 ++ up.take 63) i)
            (tips i)).2]) =
          (List.range 42).flatMap fun i =>
          [(Words.chainFrom i (toWord (val e0 0)) (w64 val p0, w64 val p1) ((Words.digits (dig val d)).getD i 0)
            (tips i)).1,
           (Words.chainFrom i (toWord (val e0 0)) (w64 val p0, w64 val p1) ((Words.digits (dig val d)).getD i 0)
            (tips i)).2] :=
        flatMap_range_congr fun j hj => by rw [hdig j hj]
      have hleaf : dig val node0 = Words.leaf (toWord (val e0 0)) (w64 val p0, w64 val p1)
          (List.ofFn fun i : Fin 42 => Words.chainFrom i (toWord (val e0 0)) (w64 val p0, w64 val p1)
            ((Words.digits (dig val d)).getD i 0) (tips i)) := by
        unfold Words.leaf
        apply dig_th
        rw [hnode0v st val (hsat.mono (by ext_chain)), hidxe, hF, List.map_append, htips, hcong]
        simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      -- The root.
      have hroot : val root = ![val node 0, val node 1, 0, 0] := by
        obtain ⟨q0, q1, q2, q3⟩ := hrootv st val (hsat.mono he24)
        exact fun4 (q0.trans (hrsv st val (hsat.mono (by ext_chain)) 0))
          (q1.trans (hrsv st val (hsat.mono (by ext_chain)) 1))
          (q2.trans (limb_zero (hzv st val (hsat.mono (by ext_chain))) 0)) q3
      refine ⟨(w64 val p0, w64 val p1), dig val node, (w64 val m0, w64 val m1, w64 val m2, w64 val m3),
        toWord (val e0 0), ⟨hlt, ?_, ?_, ?_, ?_, ?_⟩,
        ⟨⟨fun i => tips i, (w64 val r0, w64 val r1, w64 val r2), fun l => path l⟩, ?_⟩⟩
      · rw [hpv st val (hsat.mono (by ext_chain))]; exact (limbs3_two _ _).symm
      · rw [← hst1, hmv1 st val (hsat.mono (by ext_chain))]; exact (limbs3_two _ _).symm
      · rw [show s.statement + 2 = s2.statement by omega, hmv2 st val (hsat.mono (by ext_chain))]
        exact (limbs3_two _ _).symm
      · rw [show s.statement + 3 = s3.statement by omega, hev st val (hsat.mono (by ext_chain))]
        exact (limbs3_one _).symm
      · rw [show s.statement + 4 = s23.statement by omega, ← hx st val hsat, hroot]
        exact (limbs3_two _ _).symm
      · simp only [Words.verify, henc, Option.elim_some, beq_iff_eq]
        rw [climb_eq, ← hleaf, ← hpath]

/-- The circuit of `n` signatures: each signature's 99 distinct `STEP` rows and 42 `LINK` rows, its rows under every
satisfying assignment, and its statement when its tuples balance. -/
theorem circuit_good (n : ℕ) (hn : n ≤ 2 ^ 22) : Good (fun s => s.statement = 0) (Circuit.circuit n) fun _ _ s' =>
    ∃ Rs Ls : ℕ → List (List ℕ), (∀ j < n, (Rs j).length = 99 ∧ (Ls j).length = 42 ∧ (Rs j).Nodup ∧
      (∀ r ∈ Rs j, r ∈ s'.step) ∧ ∀ r ∈ Ls j, r ∈ s'.link) ∧
    ∀ st val, Sat st s' val → ∀ j < n, SigRows j val (Rs j) (Ls j) ∧ (LocalBal val (Rs j) (Ls j) →
      ∃ pp root msg epoch, Encodes st j pp root msg epoch ∧ ∃ sig, Words.verify pp root msg epoch sig = true) := by
  unfold Circuit.circuit
  refine good_of_post fun s hs h0 => ?_
  refine post_bind (forIn_range_post n _ (fun k (_ : PUnit) s' => s'.statement = 5 * k ∧
      ∃ Rs Ls : ℕ → List (List ℕ), (∀ j < k, (Rs j).length = 99 ∧ (Ls j).length = 42 ∧ (Rs j).Nodup ∧
        (∀ r ∈ Rs j, r ∈ s'.step) ∧ ∀ r ∈ Ls j, r ∈ s'.link) ∧
      ∀ st val, Sat st s' val → ∀ j < k, SigRows j val (Rs j) (Ls j) ∧ (LocalBal val (Rs j) (Ls j) →
        ∃ pp root msg epoch, Encodes st j pp root msg epoch ∧ ∃ sig, Words.verify pp root msg epoch sig = true))
      hs ⟨by omega, fun _ => [], fun _ => [], fun j hj => absurd hj (Nat.not_lt_zero j),
        fun _ _ _ j hj => absurd hj (Nat.not_lt_zero j)⟩ ?_) ?_
  · rintro k hk u s1 hi1 he1 ⟨hst1, Rs, Ls, hrows, hv1⟩
    refine (signature_good k (by omega)).step hi1 trivial ?_
    rintro _ s2 hi2 he2 ⟨hst2, R, L, hRl, hLl, hRn, hRm, hLm, hsig⟩
    refine post_pure hi2 he2 ⟨PUnit.unit, rfl, by omega, fun j => if j = k then R else Rs j,
      fun j => if j = k then L else Ls j, fun j hj => ?_, fun st val hsat j hj => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · simp only [if_neg (Nat.ne_of_lt hj)]
        obtain ⟨h1, h2, h3, h4, h5⟩ := hrows j hj
        exact ⟨h1, h2, h3, fun r hr => he2.steps _ (h4 r hr), fun r hr => he2.links _ (h5 r hr)⟩
      · simp only [if_true]
        exact ⟨hRl, hLl, hRn, hRm, hLm⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · simp only [if_neg (Nat.ne_of_lt hj)]
        exact hv1 st val (hsat.mono he2) j hj
      · simp only [if_true]
        obtain ⟨hr, hl⟩ := hsig st val hsat
        refine ⟨hr, fun hb => ?_⟩
        obtain ⟨pp, root, msg, epoch, henc, hv⟩ := hl hb
        rw [hst1] at henc
        exact ⟨pp, root, msg, epoch, henc, hv⟩
  · rintro u s1 hi1 he1 ⟨-, hv⟩
    exact post_pure hi1 he1 hv

/-- Soundness: in every assignment the machine accepts the circuit of `n` signatures with (its rows satisfied and its
dynamic bus balanced), statement words `5j .. 5j + 4` encode a parameter, root, message and epoch for which some
signature verifies. -/
theorem sound (n : ℕ) (hn : n ≤ 2 ^ 22) (st : ℕ → Fin 4 → K) (val : Val)
    (h : Accepts st ((Circuit.circuit n).run {}).2 val) :
    ∀ j < n, ∃ pp root msg epoch, Encodes st j pp root msg epoch ∧ ∃ sig, Words.verify pp root msg epoch sig = true := by
  obtain ⟨hsat, hbal⟩ := h
  obtain ⟨Rs, Ls, hrows, hv⟩ := (circuit_good n hn {} inv_empty rfl).2.2
  have hfacts := hv st val hsat
  have hsize := count_circuit n {}
  simp only [Array.size_empty, Nat.zero_add] at hsize
  have hRnd := nodup_flatMap_label n Rs (fun r => toWord (val (r.getD 4 0) 0) / 2 ^ 41)
    (fun j hj => (hrows j hj).2.2.1) fun j hj => (hfacts j hj).1.1
  have hLnd := nodup_flatMap_label n Ls (fun r => toWord (val (r.getD 0 0) 0) / 2 ^ 41 % 2 ^ 22)
    (fun j hj => (hfacts j hj).1.2.1) fun j hj => (hfacts j hj).1.2.2.1
  have hR := rows_perm _ n 99 Rs hsize.1 (fun j hj => (hrows j hj).1) (fun j hj => (hrows j hj).2.2.2.1) hRnd
  have hL := rows_perm _ n 42 Ls hsize.2 (fun j hj => (hrows j hj).2.1) (fun j hj => (hrows j hj).2.2.2.2) hLnd
  have hloc := local_of_balanced _ val n Rs Ls hR hL hbal fun j hj => (hfacts j hj).1.2.2.2
  exact fun j hj => (hfacts j hj).2 (hloc j hj)

end LeanVMCircuits.Xmss
