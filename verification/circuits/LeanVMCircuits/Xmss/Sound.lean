module

public import LeanVMCircuits.Xmss.SoundGadgets
public import LeanVMCircuits.Xmss.Statement

@[expose] public section

/-!
# Soundness of the leanXMSS circuit

In every assignment satisfying the circuit of `n` signatures, statement words `5j .. 5j + 4` encode a public
parameter, a root, a message and an epoch below `2^32` for which some signature verifies over words
(`Words.verify`). The signature is read off the assignment: the chain elements, the randomness and the siblings are
the circuit's free wires.

Per signature (`signature_good`): the statement words decode by the `CAST` rows' views and the zeros held to their
top words; the epoch's bits are its split's, the top 32 held zero; the encoding's digest is its hash row chain's,
its digits the splits of its first two words, which sum to 195 because their product reaches `x^195`; each chain is
the selection of its element at its digit, and the path climbs on the epoch's bits to the exposed root.
-/

namespace LeanVMCircuits.Xmss

open LeanVMCircuits.Rec (K E toE emb ofWord toWord words4 digest hashWords num root toE_injective)
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

/-! One signature. -/

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

theorem signature_good : Good (fun _ => True) Circuit.signature fun s _ s' => s'.statement = s.statement + 5 ∧
    ∀ st val, Sat st s' val → ∃ pp root msg epoch, EncodesAt st s.statement pp root msg epoch ∧
      ∃ sig, Words.verify pp root msg epoch sig = true := by
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
  refine post_bind (forIn_range_post 42 _ (fun k (ends : List ℕ) s' => s'.statement = s.statement + 4 ∧
      ends.length = 2 * k ∧ Wires ends s' ∧ ∀ st val, Sat st s' val → ∃ tips : ℕ → Dig,
        ends.map (w64 val) = (List.range k).flatMap fun i =>
          [(Words.chainFrom i (toWord (val e0 0)) (w64 val p0, w64 val p1) (dval val (lo.take 63 ++ up.take 63) i)
            (tips i)).1,
           (Words.chainFrom i (toWord (val e0 0)) (w64 val p0, w64 val p1) (dval val (lo.take 63 ++ up.take 63) i)
            (tips i)).2]) hi18
      ⟨by omega, rfl, Wires.nil', fun _ _ _ => ⟨fun _ => (0, 0), rfl⟩⟩ ?_) ?_
  · rintro i hi ends s19 hi19 he19 ⟨hst19, hlen19, hw19, hv19⟩
    refine fresh_good'.step hi19 trivial ?_
    rintro tip s20 hi20 he20 ⟨hst20, htip⟩
    refine (indicators_good _ _ _).step hi20 (Wires.cons' (wires_getD' (hDBw.mono (by ext_chain)) (by omega))
      (Wires.cons' (wires_getD' (hDBw.mono (by ext_chain)) (by omega))
        (Wires.cons' (wires_getD' (hDBw.mono (by ext_chain)) (by omega)) Wires.nil'))) ?_
    rintro ind s21 hi21 he21 ⟨hst21, hindlen, hindw, hindv⟩
    refine (chainEnd_good i idx tip p0 p1 ind).step hi21 ⟨lt_mono hidx (by ext_chain), lt_mono htip he21,
      lt_mono hp0 (by ext_chain), lt_mono hp1 (by ext_chain), hindw, hindlen⟩ ?_
    rintro ⟨n0, n1⟩ s22 hi22 he22 ⟨hst22, hn0, hn1, hnv⟩
    try dsimp only
    refine post_pure hi22 (by ext_chain) ⟨ends ++ [n0, n1], rfl, by omega, by simp [hlen19]; ring,
      fun w hw => ?_, fun st val hsat => ?_⟩
    · rcases List.mem_append.mp hw with hw | hw
      · exact lt_mono (hw19 w hw) (by ext_chain)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact hn0
        · exact hn1
    · obtain ⟨hbits, hlt, hbool, hidxe, hDB⟩ := hctx st val (hsat.mono (by ext_chain))
      obtain ⟨tips, htips⟩ := hv19 st val (hsat.mono (by ext_chain))
      have hind : ∀ v < 8, ev val (ind.getD v 0) = if v = dval val (lo.take 63 ++ up.take 63) i then 1 else 0 := by
        intro v hv
        rw [hindv st val (hsat.mono he22) v hv]
        exact indv_digit _ _ _ _ (hDB _ (by omega)) (hDB _ (by omega)) (hDB _ (by omega)) v hv
      have hend : (w64 val n0, w64 val n1) = Words.chainFrom i (toWord (val e0 0)) (w64 val p0, w64 val p1)
          (dval val (lo.take 63 ++ up.take 63) i) (dig val tip) := hnv st val hsat _ (dval_lt _ _ i) _ hind hidxe
      refine ⟨fun j => if j = i then dig val tip else tips j, ?_⟩
      rw [List.map_append, htips, List.range_succ, List.flatMap_append,
        flatMap_range_congr (g := fun j => [(Words.chainFrom j (toWord (val e0 0)) (w64 val p0, w64 val p1)
          (dval val (lo.take 63 ++ up.take 63) j) (if j = i then dig val tip else tips j)).1,
          (Words.chainFrom j (toWord (val e0 0)) (w64 val p0, w64 val p1)
          (dval val (lo.take 63 ++ up.take 63) j) (if j = i then dig val tip else tips j)).2])
          fun j hj => by rw [if_neg (show ¬ j = i by omega)]]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil, if_true]
      rw [← hend]
  · rintro ends s19 hi19 he19 ⟨hst19, hlen19, hw19, hv19⟩
    refine (tweakHash_good 2 0 idx [p0, p1] ends (by simp [hlen19])).step hi19 trivial ?_
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
      refine post_pure hi24 (by ext_chain) ⟨by omega, fun st val hsat => ?_⟩
      -- Read everything off the final assignment.
      obtain ⟨hbits, hlt, hbool, hidxe, hDB⟩ := hctx st val (hsat.mono (by ext_chain))
      obtain ⟨tips, htips⟩ := hv19 st val (hsat.mono (by ext_chain))
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
      · simp only [Words.verify, henc, beq_iff_eq]
        rw [climb_eq, ← hleaf, ← hpath]

/-- The circuit of `n` signatures. -/
theorem circuit_good (n : ℕ) : Good (fun s => s.statement = 0) (Circuit.circuit n) fun _ _ s' =>
    ∀ st val, Sat st s' val → ∀ j < n, ∃ pp root msg epoch, Encodes st j pp root msg epoch ∧
      ∃ sig, Words.verify pp root msg epoch sig = true := by
  unfold Circuit.circuit
  refine good_of_post fun s hs h0 => ?_
  refine post_bind (forIn_range_post n _ (fun k (_ : PUnit) s' => s'.statement = 5 * k ∧ ∀ st val, Sat st s' val →
      ∀ j < k, ∃ pp root msg epoch, Encodes st j pp root msg epoch ∧ ∃ sig, Words.verify pp root msg epoch sig = true)
      hs ⟨by omega, fun _ _ _ j hj => absurd hj (Nat.not_lt_zero j)⟩ ?_) ?_
  · rintro k hk u s1 hi1 he1 ⟨hst1, hv1⟩
    refine signature_good.step hi1 trivial ?_
    rintro _ s2 hi2 he2 ⟨hst2, hsig⟩
    refine post_pure hi2 he2 ⟨PUnit.unit, rfl, by omega, fun st val hsat j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hv1 st val (hsat.mono he2) j hj
    · obtain ⟨pp, root, msg, epoch, henc, hv⟩ := hsig st val hsat
      rw [hst1] at henc
      exact ⟨pp, root, msg, epoch, henc, hv⟩
  · rintro u s1 hi1 he1 ⟨-, hv⟩
    exact post_pure hi1 he1 hv

/-- Soundness: in every assignment satisfying the circuit of `n` signatures, statement words `5j .. 5j + 4` encode a
parameter, root, message and epoch for which some signature verifies. -/
theorem sound (n : ℕ) (st : ℕ → Fin 4 → K) (val : Val) (h : Sat st ((Circuit.circuit n).run {}).2 val) :
    ∀ j < n, ∃ pp root msg epoch, Encodes st j pp root msg epoch ∧ ∃ sig, Words.verify pp root msg epoch sig = true :=
  (circuit_good n {} inv_empty rfl).2.2 st val h

end LeanVMCircuits.Xmss
