module

public import LeanVMCircuits.Xmss.Complete
public import LeanVMCircuits.Sphincs.Statement
public import LeanVMCircuits.Sphincs.FieldFacts
public import LeanVMCircuits.Sphincs.Paths

@[expose] public section

/-!
# Completeness of the leanSPHINCS verifier circuit

Every signature `Sphincs.Words.verify` accepts, under statement words that encode it (`Sphincs.Encodes`), extends to an
assignment the machine accepts the circuit `Sphincs.Circuit.circuit n` with (`Accepts`), for `n ≤ 2^20`. The gadgets
shared with leanXMSS (statement words, digests' words, the digit product, the chains on the dynamic bus) keep their
`Xmss.Complete` contracts; layer `lay` of signature `j` runs `chains_cg` over the base `tweak0(1, lay, 0)` and the tag
`3 j + lay`, its 103 steps the cells of digits summing to 191 (`cells_digits191`), and its chains' ends are
`Words.chainFrom`'s (`spEndsW_eq`). The new gadgets: an index word of two bit lists is the tweak's second word
`tau | j << 32`, a tweak hash `th` is BLAKE2s-256 of its words, a level and `fold` climb a tree as `Words.parent` does,
the few-time key hashes the trees' roots, and a layer encodes its message in one `leafBlock` of 52 bytes, the
counter's high bits zero, before its chains, leaf and path. The signature's contract runs them in order from what
verification found: the last leaf index is zero, each layer's encoding and root, and the top root is the statement's.
Each layer's rows on the bus balance, and they are all the circuit's rows (`Sphincs.count_circuit`, `rows_perm`), so
the whole bus balances (`balanced_of_local`).
-/

namespace LeanVMCircuits.Sphincs.Complete

open LeanVMCircuits.Rec LeanVMCircuits.Rec.Model LeanVMCircuits.Xmss.Complete
open LeanVMCircuits.Xmss (limbs3 cells cells_length map_range_getD sum_range_list stepHash rows_perm balanced_of_local
  nodup_flatMap_label)
open LeanVMCircuits.Xmss.Words (W Dig)

/-! Tweak words and bit wires. -/

/-- A tweak's second word, `tau | j << 32`. -/
def tw2 (a b : ℕ) : W := BitVec.ofNat 64 (a % 2 ^ 32 + b % 2 ^ 32 * 2 ^ 32)

theorem tweak_eq (ty lay tau p j : ℕ) :
    Words.tweak ty lay tau p j = (BitVec.ofNat 64 (Circuit.tweak0 ty lay p), tw2 tau j) := rfl

theorem tw2_zero : tw2 0 0 = 0 := rfl

/-- Wires `bs` carrying the low bits of `n`. -/
def BL (bs : List ℕ) (n : ℕ) (s : State) (v : Val) : Prop :=
  Wires bs s ∧ ∀ i < bs.length, v (bs.getD i 0) = kVal (bitK n i)

theorem BL.mono {bs : List ℕ} {n : ℕ} {s s' : State} {v : Val} (h : BL bs n s v) (he : Ext s s') : BL bs n s' v :=
  ⟨h.1.mono he, h.2⟩

theorem getD_drop'' (l : List ℕ) (k i : ℕ) : (l.drop k).getD i 0 = l.getD (k + i) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_take'' (l : List ℕ) (k i : ℕ) (hi : i < k) : (l.take k).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hi]

theorem BL.drop {bs : List ℕ} {n : ℕ} {s : State} {v : Val} (h : BL bs n s v) (k : ℕ) :
    BL (bs.drop k) (n / 2 ^ k) s v := by
  refine ⟨fun w hw => h.1 w (List.mem_of_mem_drop hw), fun i hi => ?_⟩
  rw [getD_drop'', h.2 _ (by simp at hi; omega), bitK, bitK, Nat.testBit_div_two_pow, Nat.add_comm i k]

theorem BL.take {bs : List ℕ} {n : ℕ} {s : State} {v : Val} (h : BL bs n s v) (k : ℕ) :
    BL (bs.take k) (n % 2 ^ k) s v := by
  refine ⟨fun w hw => h.1 w (List.mem_of_mem_take hw), fun i hi => ?_⟩
  simp only [List.length_take] at hi
  rw [getD_take'' _ _ _ (by omega), h.2 _ (by omega), bitK, bitK, Nat.testBit_mod_two_pow,
    decide_eq_true (show i < k by omega), Bool.true_and]

theorem BL.bool {bs : List ℕ} {n : ℕ} {s : State} {v : Val} (h : BL bs n s v) :
    ∀ i < bs.length, v (bs.getD i 0) = kVal 0 ∨ v (bs.getD i 0) = kVal 1 := by
  intro i hi
  rw [h.2 i hi, bitK]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem BL.of_bitsOf {bs : List ℕ} {n : ℕ} {s : State} {v : Val} (h : BitsOf bs n s v) : BL bs n s v :=
  ⟨h.2.1, fun i hi => h.2.2 i (by rw [h.1] at hi; exact hi)⟩

theorem bitK_append (x y L i : ℕ) (hx : x < 2 ^ L) :
    bitK (x + y * 2 ^ L) i = if i < L then bitK x i else bitK y (i - L) := by
  rw [bitK, show x + y * 2 ^ L = 2 ^ L * y + x by ring, Nat.testBit_two_pow_mul_add _ hx]
  split_ifs <;> simp_all [bitK]

theorem BL.append {a b : List ℕ} {x y : ℕ} {s : State} {v : Val} (ha : BL a x s v) (hb : BL b y s v)
    (hx : x < 2 ^ a.length) : BL (a ++ b) (x + y * 2 ^ a.length) s v := by
  refine ⟨fun w hw => ?_, fun i hi => ?_⟩
  · rcases List.mem_append.mp hw with hw | hw
    · exact ha.1 w hw
    · exact hb.1 w hw
  · simp only [List.length_append] at hi
    rw [bitK_append x y _ i hx]
    by_cases hia : i < a.length
    · rw [if_pos hia, List.getD_eq_getElem?_getD, List.getElem?_append_left hia, ← List.getD_eq_getElem?_getD]
      exact ha.2 i hia
    · rw [if_neg hia, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
        ← List.getD_eq_getElem?_getD]
      exact hb.2 _ (by omega)

theorem idx_getD' (tau j : List ℕ) (z i : ℕ) (htau : tau.length ≤ 32) :
    (tau ++ List.replicate (32 - tau.length) z ++ j).getD i 0 =
      if i < tau.length then tau.getD i 0 else if i < 32 then z else j.getD (i - 32) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append, List.length_append, List.length_replicate]
  by_cases h1 : i < tau.length
  · rw [if_pos (show i < tau.length + (32 - tau.length) by omega), if_pos h1, List.getElem?_append_left h1,
      List.getD_eq_getElem?_getD]
  · by_cases h2 : i < 32
    · rw [if_pos (show i < tau.length + (32 - tau.length) by omega), if_neg h1, if_pos h2,
        List.getElem?_append_right (show tau.length ≤ i by omega), List.getElem?_replicate,
        if_pos (show i - tau.length < 32 - tau.length by omega)]
      rfl
    · rw [if_neg (show ¬ i < tau.length + (32 - tau.length) by omega), if_neg h1, if_neg h2,
        List.getD_eq_getElem?_getD, show i - (tau.length + (32 - tau.length)) = i - 32 by omega]

theorem sp_index_num (a b ta tj : ℕ) (hta : ta ≤ 32) (htj : tj ≤ 32) (ha : a < 2 ^ ta) (hb : b < 2 ^ tj)
    (c : ℕ → ZMod 2)
    (hc : ∀ i < 64, (c i = 1 ↔ (i < ta ∧ a.testBit i = true) ∨ (32 ≤ i ∧ i < 32 + tj ∧ b.testBit (i - 32) = true))) :
    num c 64 = (tw2 a b).toNat := by
  have ha32 : a < 2 ^ 32 := lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hta)
  have hb32 : b < 2 ^ 32 := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) htj)
  have h64 : a + b * 2 ^ 32 < 2 ^ 64 := by
    calc a + b * 2 ^ 32 < 2 ^ 32 + b * 2 ^ 32 := by omega
      _ = (b + 1) * 2 ^ 32 := by ring
      _ ≤ 2 ^ 32 * 2 ^ 32 := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ 64 := by norm_num
  rw [tw2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha32, Nat.mod_eq_of_lt hb32, Nat.mod_eq_of_lt h64]
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · rw [testBit_num c 64 i hi, show a + b * 2 ^ 32 = 2 ^ 32 * b + a by ring, Nat.testBit_two_pow_mul_add _ ha32]
    have := hc i hi
    by_cases h32 : i < 32
    · rw [if_pos h32]
      by_cases hia : i < ta
      · by_cases hab : a.testBit i = true
        · rw [hab]; simp only [decide_eq_true_eq]; exact this.mpr (Or.inl ⟨hia, hab⟩)
        · simp only [Bool.not_eq_true] at hab
          rw [hab]; simp only [decide_eq_false_iff_not]
          intro hc1; rcases this.mp hc1 with ⟨-, h⟩ | ⟨h, -⟩
          · rw [hab] at h; exact absurd h (by simp)
          · omega
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega)))]
        simp only [decide_eq_false_iff_not]
        intro hc1; rcases this.mp hc1 with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
    · rw [if_neg h32]
      by_cases hij : i < 32 + tj
      · by_cases hbb : b.testBit (i - 32) = true
        · rw [hbb]; simp only [decide_eq_true_eq]; exact this.mpr (Or.inr ⟨by omega, hij, hbb⟩)
        · simp only [Bool.not_eq_true] at hbb
          rw [hbb]; simp only [decide_eq_false_iff_not]
          intro hc1; rcases this.mp hc1 with ⟨h, -⟩ | ⟨-, -, h⟩
          · omega
          · rw [hbb] at h; exact absurd h (by simp)
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))]
        simp only [decide_eq_false_iff_not]
        intro hc1; rcases this.mp hc1 with ⟨h, -⟩ | ⟨-, h, -⟩ <;> omega
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (num_lt c 64) (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem ite_zmod_one (P : Prop) [Decidable P] : ((if P then (1 : ZMod 2) else 0) = 1) ↔ P := by
  split_ifs with h <;> simp [h]

section

variable {st : ℕ → Fin 4 → K}

/-- `indexWord`: the word `tau | j << 32` of the bits of `a` and `b`. -/
theorem spIndexWord_cg (tau j : List ℕ) (a b : ℕ) (htau : tau.length ≤ 32) (hj : j.length ≤ 32)
    (ha : a < 2 ^ tau.length) (hb : b < 2 ^ j.length) :
    CGood st 0 (fun s v => BL tau a s v ∧ BL j b s v) (Circuit.indexWord tau j)
      fun _ r s' v => r < s'.next ∧ v r = kw (tw2 a b) := by
  unfold Circuit.indexWord
  refine CGood.seq (k₂ := 0) ((kConst_cgood 0).pre (P' := fun s v => BL tau a s v ∧ BL j b s v)
      fun _ _ _ => trivial)
    (P₂ := fun z s v => BL tau a s v ∧ BL j b s v ∧ z < s.next ∧ v z = kVal 0)
    (fun _ _ _ _ _ hp he hq => ⟨hp.1.mono he, hp.2.mono he, hq.1, by rw [hq.2, ofWord_zero]⟩) fun z => ?_
  split_ifs with hemp
  · simp only [Bool.and_eq_true, List.isEmpty_iff] at hemp
    obtain ⟨rfl, rfl⟩ := hemp
    simp only [List.length_nil, pow_zero, Nat.lt_one_iff] at ha hb
    subst ha; subst hb
    exact CGood.pure' fun s v _ h => ⟨h.2.2.1, by rw [h.2.2.2, tw2_zero, kw_zero]⟩
  · have hL : (tau ++ List.replicate (32 - tau.length) z ++ j).length = 32 + j.length := by
      simp only [List.length_append, List.length_replicate]; omega
    refine ((pack_cgood _).pre fun s v h => ⟨fun w hw => ?_, by rw [hL]; omega, fun i hi => ?_⟩).weaken
      (fun _ _ h => h) ?_
    · simp only [List.mem_append] at hw
      rcases hw with (hw | hw) | hw
      · exact h.1.1 w hw
      · rw [List.eq_of_mem_replicate hw]; exact h.2.2.1
      · exact h.2.1.1 w hw
    · rw [idx_getD' tau j z i htau]
      split_ifs with h1 h2
      · exact h.1.bool i h1
      · exact Or.inl h.2.2.2
      · exact h.2.1.bool _ (by rw [hL] at hi; omega)
    · rintro s r s' v _ ⟨hta, hjb, hz, hzv⟩ _ ⟨hr, hrv⟩
      refine ⟨hr, ?_⟩
      have hk01 : kVal (0 : K) ≠ kVal 1 := fun h => zero_ne_one (kVal_inj h)
      rw [hrv, kw, sp_index_num a b _ _ htau hj ha hb]
      intro i hi
      rw [ite_zmod_one, hL, idx_getD' tau j z i htau]
      by_cases h1 : i < tau.length
      · rw [if_pos h1, hta.2 i h1, kVal_bitK_eq_one]
        constructor
        · rintro ⟨-, h2⟩
          exact Or.inl ⟨h1, h2⟩
        · rintro (⟨-, h2⟩ | ⟨h2, -⟩)
          · exact ⟨by omega, h2⟩
          · omega
      · rw [if_neg h1]
        by_cases h2 : i < 32
        · rw [if_pos h2, hzv]
          constructor
          · rintro ⟨-, h3⟩
            exact absurd h3 hk01
          · rintro (⟨h3, -⟩ | ⟨h3, -⟩) <;> omega
        · rw [if_neg h2]
          by_cases h3 : i - 32 < j.length
          · rw [hjb.2 _ h3, kVal_bitK_eq_one]
            constructor
            · rintro ⟨h4, h5⟩
              exact Or.inr ⟨by omega, h4, h5⟩
            · rintro (⟨h4, -⟩ | ⟨-, h4, h5⟩)
              · omega
              · exact ⟨h4, h5⟩
          · constructor
            · rintro ⟨h4, -⟩
              omega
            · rintro (⟨h4, -⟩ | ⟨-, h4, -⟩) <;> omega

/-- `th`: the hash of `tw0 || tw1 || pp || payload`. -/
theorem th_cg (tw0 : ℕ) (htw : tw0 < 2 ^ 64) (tw1 : ℕ) (pp payload : List ℕ)
    (hlen : pp.length + payload.length ≤ 100) :
    CGood st 0 (fun s v => Wires (tw1 :: pp ++ payload) s ∧ ∀ w ∈ tw1 :: pp ++ payload, v w = kVal (v w 0))
      (Circuit.th tw0 tw1 pp payload) fun _ d s' v => d < s'.next ∧
        v d = dVal (digest (hashWords (BitVec.ofNat 64 tw0 :: (tw1 :: pp ++ payload).map (w64 v)))) := by
  have hb : ∀ t : ℕ, 8 * ([t, tw1] ++ pp ++ payload).length < 2 ^ 64 := fun t => by
    simp only [List.length_append, List.length_cons, List.length_nil]
    have : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
    omega
  have hk : ∀ (t : ℕ) (v : Val), (∀ w ∈ tw1 :: pp ++ payload, v w = kVal (v w 0)) →
      v t = kVal (ofWord tw0) → ∀ w ∈ t :: tw1 :: pp ++ payload, v w = kVal (v w 0) := by
    intro t v hp ht w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact kVal_isK ht
    · exact hp w hw
  unfold Circuit.th
  refine (CGood.bind ((kConst_cgood _).pre (P' := fun s v => Wires (tw1 :: pp ++ payload) s ∧
      ∀ w ∈ tw1 :: pp ++ payload, v w = kVal (v w 0)) fun _ _ _ => trivial)
    (P₂ := fun t s v => Wires (t :: tw1 :: pp ++ payload) s ∧
      (∀ w ∈ t :: tw1 :: pp ++ payload, v w = kVal (v w 0)) ∧ v t = kVal (ofWord tw0))
    (fun _ t _ v _ hp he hq => ⟨wires_cons.2 ⟨hq.1, hp.1.mono he⟩, hk t v hp.2 hq.2, hq.2⟩)
    fun t => (chain_cgood ([t, tw1] ++ pp ++ payload) (hb t)).pre fun _ _ h => ⟨h.1, h.2.1⟩).weaken
    (fun _ _ h => h) ?_
  rintro s d s2 v hs - - ⟨t, s1, -, -, -, ⟨htl, htv⟩, hd, hdv⟩
  refine ⟨hd, ?_⟩
  have hw : w64 v t = BitVec.ofNat 64 tw0 := by
    rw [w64, htv, kVal_apply_zero, toWord_ofWord _ htw]
  have hl : ([t, tw1] ++ pp ++ payload).map (w64 v) =
      BitVec.ofNat 64 tw0 :: (tw1 :: pp ++ payload).map (w64 v) := by
    simp only [List.cons_append, List.nil_append, List.map_cons, hw]
  rw [hdv, hl]

end

theorem sp_th_words (tw0 : ℕ) (T1 : W) (p : Dig) (tw1 : ℕ) (pp payload : List ℕ) (v : Val) {s : State}
    (h1 : v tw1 = kw T1) (hpp : PPw pp p s v) :
    BitVec.ofNat 64 tw0 :: (tw1 :: pp ++ payload).map (w64 v) =
      [BitVec.ofNat 64 tw0, T1, p.1, p.2] ++ payload.map (w64 v) := by
  simp [List.map_append, hpp.map, w64_kw h1]

theorem sp_dVal_th (tw : W × W) (p : Dig) (ws : List W) :
    (digest (hashWords ([tw.1, tw.2, p.1, p.2] ++ ws)) 0, digest (hashWords ([tw.1, tw.2, p.1, p.2] ++ ws)) 1) =
      Words.th tw p ws := rfl

theorem sp_tw_bound (ty lay p : ℕ) (hty : ty < 256) (hlay : lay < 256) (hp : p < 2 ^ 32) :
    Circuit.tweak0 ty lay p < 2 ^ 64 := by
  unfold Circuit.tweak0
  have h1 : (2 : ℕ) ^ 8 = 256 := by norm_num
  have h2 : (2 : ℕ) ^ 16 = 65536 := by norm_num
  have h3 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  have h4 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
  rw [h1, h2, h3, h4]
  rw [h3] at hp
  omega

section

variable {st : ℕ → Fin 4 → K}

def SLCtx (idx bit node : ℕ) (pp : List ℕ) (T1 : W) (p : Dig) (β : Bool) (D : Fin 4 → W) (s : State)
    (v : Val) : Prop :=
  idx < s.next ∧ v idx = kw T1 ∧ PPw pp p s v ∧ bit < s.next ∧
    v bit = kVal (if β then 1 else 0) ∧ node < s.next ∧ v node = dVal D

theorem SLCtx.mono {idx bit node : ℕ} {pp : List ℕ} {T1 : W} {p : Dig} {β : Bool} {D : Fin 4 → W}
    {s s' : State} {v : Val} (h : SLCtx idx bit node pp T1 p β D s v) (he : Ext s s') :
    SLCtx idx bit node pp T1 p β D s' v :=
  ⟨lt_of_lt_of_le h.1 he.next, h.2.1, h.2.2.1.mono he, lt_of_lt_of_le h.2.2.2.1 he.next, h.2.2.2.2.1,
    lt_of_lt_of_le h.2.2.2.2.2.1 he.next, h.2.2.2.2.2.2⟩

/-- `level`: the parent of the node and the sibling `S`, the node on the side the bit names. -/
theorem spLevel_cg (tw0 : ℕ) (htw : tw0 < 2 ^ 64) (idx bit node : ℕ) (pp : List ℕ) (T1 : W) (p S : Dig) (β : Bool)
    (D : Fin 4 → W) (hpl : pp.length = 2) :
    CGood st 0 (fun s v => SLCtx idx bit node pp T1 p β D s v) (Circuit.level tw0 idx bit node pp)
      fun _ r s' v => r < s'.next ∧ v r = dVal (digest (hashWords ([BitVec.ofNat 64 tw0, T1, p.1, p.2] ++
        if β then [S.1, S.2, D 0, D 1] else [D 0, D 1, S.1, S.2]))) := by
  unfold Circuit.level
  refine CGood.seq (k₂ := 0) ((dToEAndK_cgood node).pre fun s v h => h.2.2.2.2.2.1)
    (P₂ := fun a s v => SLCtx idx bit node pp T1 p β D s v ∧ a.1 < s.next ∧ v a.1 = cv D)
    (fun s a s' v _ hp he hq => ⟨hp.mono he, hq.1, by rw [hq.2.2.1, hp.2.2.2.2.2.2]; rfl⟩) fun a => ?_
  obtain ⟨cur, sn⟩ := a
  try dsimp only
  refine CGood.seq (k₂ := 0) ((wire_cgood (limbs3 S.1 S.2 0)).pre fun _ _ _ => trivial)
    (P₂ := fun sib s v => SLCtx idx bit node pp T1 p β D s v ∧ cur < s.next ∧ v cur = cv D ∧ sib < s.next ∧
      v sib = limbs3 S.1 S.2 0)
    (fun s sib s' v _ hp he hq => ⟨hp.1.mono he, lt_of_lt_of_le hp.2.1 he.next, hp.2.2,
      by rw [hq.2.1, hq.1]; exact Nat.lt_succ_self _, hq.2.2⟩) fun sib => ?_
  refine CGood.seq (k₂ := 0) ((add_cgood cur sib).pre fun s v h => ⟨wires2 h.2.1 h.2.2.2.1,
      by rw [h.2.2.1]; rfl, by rw [h.2.2.2.2]; rfl⟩)
    (P₂ := fun diff s v => (SLCtx idx bit node pp T1 p β D s v ∧ cur < s.next ∧ v cur = cv D ∧ sib < s.next ∧
      v sib = limbs3 S.1 S.2 0) ∧ diff < s.next ∧ v diff = eVal (ev v cur + ev v sib))
    (fun s diff s' v _ hp he hq => ⟨⟨hp.1.mono he, lt_of_lt_of_le hp.2.1 he.next, hp.2.2.1,
      lt_of_lt_of_le hp.2.2.2.1 he.next, hp.2.2.2.2⟩, hq⟩) fun diff => ?_
  refine CGood.seq (k₂ := 0) ((mulKAdd_cgood diff bit cur).pre fun s v h => ⟨wires3 h.2.1 h.1.1.2.2.2.1 h.1.2.1,
      by rw [h.2.2]; rfl, kVal_isK h.1.1.2.2.2.2.1, by rw [h.1.2.2.1]; rfl⟩)
    (P₂ := fun left s v => ((SLCtx idx bit node pp T1 p β D s v ∧ cur < s.next ∧ v cur = cv D ∧ sib < s.next ∧
      v sib = limbs3 S.1 S.2 0) ∧ diff < s.next ∧ v diff = eVal (ev v cur + ev v sib)) ∧ left < s.next ∧
      v left = if β then v sib else v cur)
    (fun s left s' v _ hp he hq => by
      refine ⟨⟨⟨hp.1.1.mono he, lt_of_lt_of_le hp.1.2.1 he.next, hp.1.2.2.1, lt_of_lt_of_le hp.1.2.2.2.1 he.next,
        hp.1.2.2.2.2⟩, lt_of_lt_of_le hp.2.1 he.next, hp.2.2⟩, hq.1, ?_⟩
      rw [hq.2, ev_of_eVal hp.2.2]
      exact sel_left v cur sib bit β hp.1.1.2.2.2.2.1 (by rw [hp.1.2.2.1]; rfl) (by rw [hp.1.2.2.2.2]; rfl))
    fun left => ?_
  refine CGood.seq (k₂ := 0) ((add_cgood left diff).pre fun s v h => ⟨wires2 h.2.1 h.1.2.1,
      by rw [h.2.2]; exact ite_three β _ _ (by rw [h.1.1.2.2.2.2]; rfl) (by rw [h.1.1.2.2.1]; rfl),
      by rw [h.1.2.2]; rfl⟩)
    (P₂ := fun right s v => SLCtx idx bit node pp T1 p β D s v ∧ left < s.next ∧ right < s.next ∧
      v left = (if β then limbs3 S.1 S.2 0 else cv D) ∧ v right = (if β then cv D else limbs3 S.1 S.2 0))
    (fun s right s' v _ hp he hq => by
      obtain ⟨⟨⟨hc, hcur, hcv, hsib, hsv⟩, hd, hdv⟩, hl, hlv⟩ := hp
      refine ⟨hc.mono he, lt_of_lt_of_le hl he.next, hq.1, by rw [hlv, hcv, hsv], ?_⟩
      rw [hq.2, ev_of_eVal hdv, sel_right v cur sib left β hlv (by rw [hcv]; rfl) (by rw [hsv]; rfl), hcv, hsv])
    fun right => ?_
  refine CGood.seq (k₂ := 0) ((words_cg left).pre fun s v h => ⟨h.2.1, by rw [h.2.2.2.1]; split_ifs <;> rfl⟩)
    (P₂ := fun a s v => SLCtx idx bit node pp T1 p β D s v ∧ right < s.next ∧
      v right = (if β then cv D else limbs3 S.1 S.2 0) ∧ a.1 < s.next ∧ a.2.1 < s.next ∧
      v a.1 = kw (if β then S else (D 0, D 1)).1 ∧ v a.2.1 = kw (if β then S else (D 0, D 1)).2)
    (fun s a s' v _ hp he hq => by
      obtain ⟨hc, hl, hr, hlv, hrv⟩ := hp
      refine ⟨hc.mono he, lt_of_lt_of_le hr he.next, hrv, hq.1.1, hq.1.2.1, ?_, ?_⟩
      · rw [hq.2.1, hlv]; cases β <;> rfl
      · rw [hq.2.2.1, hlv]; cases β <;> rfl)
    fun a => ?_
  obtain ⟨l0, l1, sn2⟩ := a
  try dsimp only
  refine CGood.seq (k₂ := 0) ((words_cg right).pre fun s v h => ⟨h.2.1, by rw [h.2.2.1]; split_ifs <;> rfl⟩)
    (P₂ := fun a s v => SLCtx idx bit node pp T1 p β D s v ∧ l0 < s.next ∧ l1 < s.next ∧
      v l0 = kw (if β then S else (D 0, D 1)).1 ∧ v l1 = kw (if β then S else (D 0, D 1)).2 ∧
      a.1 < s.next ∧ a.2.1 < s.next ∧
      v a.1 = kw (if β then (D 0, D 1) else S).1 ∧ v a.2.1 = kw (if β then (D 0, D 1) else S).2)
    (fun s a s' v _ hp he hq => by
      obtain ⟨hc, hr, hrv, h0, h1, h0v, h1v⟩ := hp
      refine ⟨hc.mono he, lt_of_lt_of_le h0 he.next, lt_of_lt_of_le h1 he.next, h0v, h1v, hq.1.1, hq.1.2.1, ?_, ?_⟩
      · rw [hq.2.1, hrv]; cases β <;> rfl
      · rw [hq.2.2.1, hrv]; cases β <;> rfl)
    fun a => ?_
  obtain ⟨r0, r1, sn3⟩ := a
  try dsimp only
  refine ((th_cg tw0 htw idx pp [l0, l1, r0, r1] (by simp [hpl])).pre fun s v h => ?_).weaken (fun _ _ h => h) ?_
  · obtain ⟨hc, h0, h1, h0v, h1v, h2, h3, h2v, h3v⟩ := h
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw
      rcases hw with (rfl | hw) | rfl | rfl | rfl | rfl
      · exact hc.1
      · exact hc.2.2.1.2.1 w hw
      · exact h0
      · exact h1
      · exact h2
      · exact h3
    · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw
      rcases hw with (rfl | hw) | rfl | rfl | rfl | rfl
      · exact kw_isK hc.2.1
      · exact hc.2.2.1.isK w hw
      · exact kw_isK h0v
      · exact kw_isK h1v
      · exact kw_isK h2v
      · exact kw_isK h3v
  · rintro s r s' v _ ⟨hc, h0, h1, h0v, h1v, h2, h3, h2v, h3v⟩ - ⟨hr, hrv⟩
    refine ⟨hr, ?_⟩
    rw [hrv, sp_th_words tw0 T1 p idx pp [l0, l1, r0, r1] v hc.2.1 hc.2.2.1]
    simp only [List.map_cons, List.map_nil, w64_kw h0v, w64_kw h1v, w64_kw h2v, w64_kw h3v]
    cases β <;> rfl

end

/-! Climbing a tree. -/

/-- The first `l` levels of a climb from `lf`. -/
def climbP (ty lay t e : ℕ) (p : Dig) (path : ℕ → Dig) (lf : Dig) (l : ℕ) : Dig :=
  (List.range l).foldl (fun cur l => Words.parent ty lay t e l p cur (path l)) lf

theorem climbP_succ (ty lay t e : ℕ) (p : Dig) (path : ℕ → Dig) (lf : Dig) (l : ℕ) :
    climbP ty lay t e p path lf (l + 1) = Words.parent ty lay t e l p (climbP ty lay t e p path lf l) (path l) := by
  simp [climbP, List.range_succ]

theorem climb_eq' (ty lay t e h : ℕ) (p : Dig) (path : Fin h → Dig) (pathN : ℕ → Dig)
    (hpath : ∀ l (hl : l < h), path ⟨l, hl⟩ = pathN l) (lf : Dig) :
    Words.climb ty lay t e h p path lf = climbP ty lay t e p pathN lf h := by
  have hf : (fun cur (l : Fin h) => Words.parent ty lay t e l.val p cur (path l)) =
      fun c (l : Fin h) => (fun cur l => Words.parent ty lay t e l p cur (pathN l)) c l.val := by
    funext cur l; rw [hpath l.val l.isLt]
  unfold Words.climb
  rw [hf]
  exact foldl_finRange h (fun cur l => Words.parent ty lay t e l p cur (pathN l)) lf

section

variable {st : ℕ → Fin 4 → K}

/-- A climb's context: the tree's and the leaf's bits, the top tweak word and the parameter. -/
def FCtx (tauBits jBits : List ℕ) (top : ℕ) (pp : List ℕ) (t e : ℕ) (p : Dig) (s : State) (v : Val) : Prop :=
  BL tauBits t s v ∧ BL jBits e s v ∧ top < s.next ∧ v top = kw (tw2 t 0) ∧ PPw pp p s v

theorem FCtx.mono {tauBits jBits : List ℕ} {top : ℕ} {pp : List ℕ} {t e : ℕ} {p : Dig} {s s' : State} {v : Val}
    (h : FCtx tauBits jBits top pp t e p s v) (he : Ext s s') : FCtx tauBits jBits top pp t e p s' v :=
  ⟨h.1.mono he, h.2.1.mono he, lt_of_lt_of_le h.2.2.1 he.next, h.2.2.2.1, h.2.2.2.2.mono he⟩

/-- `fold`: a leaf climbed to its tree's root, the sibling at level `l` being `path l`. -/
theorem fold_cg (ty lay : ℕ) (tauBits jBits : List ℕ) (top : ℕ) (pp : List ℕ) (leaf : ℕ) (t e : ℕ) (p : Dig)
    (path : ℕ → Dig) (L : Fin 4 → W) (hty : ty < 256) (hlay : lay < 256) (htau : tauBits.length ≤ 32)
    (hj : jBits.length ≤ 32) (ht : t < 2 ^ tauBits.length) (he : e < 2 ^ jBits.length) (hpl : pp.length = 2) :
    CGood st 0 (fun s v => FCtx tauBits jBits top pp t e p s v ∧ leaf < s.next ∧ v leaf = dVal L)
      (Circuit.fold ty lay tauBits jBits top pp leaf) fun _ r s' v => r < s'.next ∧
        ∃ Dn : Fin 4 → W, v r = dVal Dn ∧ (Dn 0, Dn 1) = climbP ty lay t e p path (L 0, L 1) jBits.length := by
  unfold Circuit.fold
  try dsimp only
  refine (CGood.seq (k₂ := 0) ((forIn_cgood 0 _ (List.range jBits.length)
      (fun l nd s v => FCtx tauBits jBits top pp t e p s v ∧ nd < s.next ∧
        ∃ Dn : Fin 4 → W, v nd = dVal Dn ∧ (Dn 0, Dn 1) = climbP ty lay t e p path (L 0, L 1) l) ?_ leaf).pre
      fun s v h => ⟨h.1, h.2.1, L, h.2.2, rfl⟩)
    (P₂ := fun r s v => r < s.next ∧
      ∃ Dn : Fin 4 → W, v r = dVal Dn ∧ (Dn 0, Dn 1) = climbP ty lay t e p path (L 0, L 1) jBits.length)
    (fun s r s' v _ _ _ hq => by
      obtain ⟨-, hr, Dn, h1, h2⟩ := hq
      simp only [List.length_range] at h2
      exact ⟨hr, Dn, h1, h2⟩) fun r => ?_).kEq (by simp)
  · intro l hl nd
    simp only [List.length_range] at hl
    try simp only [List.getElem_range]
    try dsimp only
    have hcont : ∀ tw1 : ℕ, CGood st 0 (fun s v => (FCtx tauBits jBits top pp t e p s v ∧ nd < s.next ∧
          ∃ Dn : Fin 4 → W, v nd = dVal Dn ∧ (Dn 0, Dn 1) = climbP ty lay t e p path (L 0, L 1) l) ∧
        tw1 < s.next ∧ v tw1 = kw (tw2 t (e / 2 ^ (l + 1))))
        (do
          let node ← Circuit.level (Circuit.tweak0 ty lay (l + 1)) tw1 (jBits.getD l 0) nd pp
          pure (ForInStep.yield node))
        fun _ r s' v => ∃ b', r = ForInStep.yield b' ∧ FCtx tauBits jBits top pp t e p s' v ∧ b' < s'.next ∧
          ∃ Dn : Fin 4 → W, v b' = dVal Dn ∧ (Dn 0, Dn 1) = climbP ty lay t e p path (L 0, L 1) (l + 1) := by
      intro tw1
      apply CGood.intro
      intro s₀ val₀
      have hD : ∀ s v, s = s₀ → Agree s.next val₀ v → nd < s.next →
          ∀ Dn : Fin 4 → W, v nd = dVal Dn → words4 (val₀ nd) = Dn := by
        intro s v hs hag hnd Dn hDn
        rw [← hag nd hnd, hDn, words4_dVal]
      refine CGood.seq (k₂ := 0) ((spLevel_cg (Circuit.tweak0 ty lay (l + 1))
          (sp_tw_bound ty lay (l + 1) hty hlay (by have : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
                                                   omega))
          tw1 (jBits.getD l 0) nd pp (tw2 t (e / 2 ^ (l + 1))) p (path l) (e.testBit l) (words4 (val₀ nd)) hpl).pre
          fun s v h => ?_)
        (P₂ := fun nd' s v => FCtx tauBits jBits top pp t e p s v ∧ nd' < s.next ∧
          ∃ Dn : Fin 4 → W, v nd' = dVal Dn ∧ (Dn 0, Dn 1) = climbP ty lay t e p path (L 0, L 1) (l + 1))
        ?_ fun nd' => ?_
      · obtain ⟨hs, hag, ⟨hc, hnd, Dn, hDn, -⟩, htw, htwv⟩ := h
        refine ⟨htw, htwv, hc.2.2.2.2, hc.2.1.1 _ (getD_mem (by omega)), by rw [hc.2.1.2 l (by omega), bitK_eq],
          hnd, by rw [hD s v hs hag hnd Dn hDn, hDn]⟩
      · rintro s nd' s' v _ ⟨hs, hag, ⟨hc, hnd, Dn, hDn, hcl⟩, -, -⟩ he ⟨hr, hrv⟩
        refine ⟨hc.mono he, hr, _, hrv, ?_⟩
        rw [climbP_succ, ← hcl, ← hD s v hs hag hnd Dn hDn]
        unfold Words.parent
        cases e.testBit l
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact sp_dVal_th (Words.tweak ty lay t (l + 1) (e / 2 ^ (l + 1))) p _
        · simp only [↓reduceIte]
          exact sp_dVal_th (Words.tweak ty lay t (l + 1) (e / 2 ^ (l + 1))) p _
      · exact CGood.pure' fun s v _ h => ⟨nd', rfl, h⟩
    have hp : ∀ s tw1 s' v, Model.Inv s → (FCtx tauBits jBits top pp t e p s v ∧ nd < s.next ∧
          ∃ Dn : Fin 4 → W, v nd = dVal Dn ∧ (Dn 0, Dn 1) = climbP ty lay t e p path (L 0, L 1) l) → Ext s s' →
        (tw1 < s'.next ∧ v tw1 = kw (tw2 t (e / 2 ^ (l + 1)))) →
        (FCtx tauBits jBits top pp t e p s' v ∧ nd < s'.next ∧
          ∃ Dn : Fin 4 → W, v nd = dVal Dn ∧ (Dn 0, Dn 1) = climbP ty lay t e p path (L 0, L 1) l) ∧
        tw1 < s'.next ∧ v tw1 = kw (tw2 t (e / 2 ^ (l + 1))) :=
      fun s tw1 s' v _ hp he hq => ⟨⟨hp.1.mono he, lt_of_lt_of_le hp.2.1 he.next, hp.2.2⟩, hq⟩
    split_ifs with hlt
    · exact CGood.seq (k₂ := 0) ((spIndexWord_cg tauBits (jBits.drop (l + 1)) t (e / 2 ^ (l + 1)) htau
          (by simp only [List.length_drop]; omega) ht (by
            simp only [List.length_drop]
            rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show jBits.length - (l + 1) + (l + 1) =
              jBits.length by omega]
            exact he)).pre fun s v h => ⟨h.1.1, h.1.2.1.drop (l + 1)⟩) hp hcont
    · exact CGood.seq (k₂ := 0) (CGood.pure' (Q := fun _ r s' v => r < s'.next ∧ v r = kw (tw2 t (e / 2 ^ (l + 1))))
          fun s v _ h => ⟨h.1.2.2.1, by
            rw [h.1.2.2.2.1, Nat.div_eq_of_lt (lt_of_lt_of_le he (Nat.pow_le_pow_right (by norm_num) (by omega)))]⟩)
        hp hcont
  · try dsimp only
    exact CGood.pure' fun s v _ h => h

end

/-! The few-time key. -/

/-- Few-time tree `κ`'s leaf: the hash of its secret. -/
def ftsLeafD (idx : ℕ) (u : ℕ → ℕ) (p : Dig) (S : ℕ → Dig) (κ : ℕ) : Fin 4 → W :=
  digest (hashWords ([BitVec.ofNat 64 (Circuit.tweak0 9 κ 0), tw2 idx (u κ), p.1, p.2] ++ [(S κ).1, (S κ).2]))

/-- Few-time tree `κ`'s root. -/
def rootW (idx : ℕ) (u : ℕ → ℕ) (p : Dig) (S : ℕ → Dig) (P : ℕ → ℕ → Dig) (κ : ℕ) : Dig :=
  climbP 10 κ idx (u κ) p (P κ) (ftsLeafD idx u p S κ 0, ftsLeafD idx u p S κ 1) 10

/-- The words of the first `k` few-time roots. -/
def rootsW (idx : ℕ) (u : ℕ → ℕ) (p : Dig) (S : ℕ → Dig) (P : ℕ → ℕ → Dig) (k : ℕ) : List W :=
  (List.range k).flatMap fun κ => [(rootW idx u p S P κ).1, (rootW idx u p S P κ).2]

theorem rootsW_succ (idx : ℕ) (u : ℕ → ℕ) (p : Dig) (S : ℕ → Dig) (P : ℕ → ℕ → Dig) (k : ℕ) :
    rootsW idx u p S P (k + 1) = rootsW idx u p S P k ++ [(rootW idx u p S P k).1, (rootW idx u p S P k).2] := by
  simp [rootsW, List.range_succ, List.flatMap_append]

theorem rootsW_length (idx : ℕ) (u : ℕ → ℕ) (p : Dig) (S : ℕ → Dig) (P : ℕ → ℕ → Dig) (k : ℕ) :
    (rootsW idx u p S P k).length = 2 * k := by
  induction k with
  | zero => simp [rootsW]
  | succ k ih => rw [rootsW_succ, List.length_append, ih]; simp; ring

theorem PPw.lw {pp : List ℕ} {p : Dig} {s : State} {v : Val} (h : PPw pp p s v) : LW pp [p.1, p.2] s v :=
  ⟨by rw [h.1]; rfl, h.2.1, fun i hi => by
    rw [h.1] at hi
    interval_cases i
    · exact h.2.2.1
    · exact h.2.2.2⟩

section

variable {st : ℕ → Fin 4 → K}

/-- The few-time key's context. -/
def FTCtx (idxBits : List ℕ) (us : List (List ℕ)) (top : ℕ) (pp : List ℕ) (idx : ℕ) (u : ℕ → ℕ) (p : Dig)
    (s : State) (v : Val) : Prop :=
  BL idxBits idx s v ∧ (∀ κ < 14, BL (us.getD κ []) (u κ) s v) ∧ top < s.next ∧ v top = kw (tw2 idx 0) ∧
    PPw pp p s v

theorem FTCtx.mono {idxBits : List ℕ} {us : List (List ℕ)} {top : ℕ} {pp : List ℕ} {idx : ℕ} {u : ℕ → ℕ}
    {p : Dig} {s s' : State} {v : Val} (h : FTCtx idxBits us top pp idx u p s v) (he : Ext s s') :
    FTCtx idxBits us top pp idx u p s' v :=
  ⟨h.1.mono he, fun κ hκ => (h.2.1 κ hκ).mono he, lt_of_lt_of_le h.2.2.1 he.next, h.2.2.2.1, h.2.2.2.2.mono he⟩

theorem fts_cg (idxBits : List ℕ) (us : List (List ℕ)) (top : ℕ) (pp : List ℕ) (idx : ℕ) (u : ℕ → ℕ) (p : Dig)
    (S : ℕ → Dig) (P : ℕ → ℕ → Dig) (hidxl : idxBits.length = 26) (hidx : idx < 2 ^ 26)
    (husl : ∀ κ < 14, (us.getD κ []).length = 10) (hu : ∀ κ < 14, u κ < 2 ^ 10) (hpl : pp.length = 2) :
    CGood st 0 (fun s v => FTCtx idxBits us top pp idx u p s v) (Circuit.fts idxBits us top pp)
      fun _ r s' v => r < s'.next ∧ v r = dVal (digest (hashWords
        ([BitVec.ofNat 64 (Circuit.tweak0 11 0 0), tw2 idx 0, p.1, p.2] ++ rootsW idx u p S P 14))) := by
  unfold Circuit.fts
  try dsimp only
  refine (CGood.seq (k₂ := 0) ((forIn_cgood 0 _ (List.range 14)
      (fun κ roots s v => FTCtx idxBits us top pp idx u p s v ∧ LW roots (rootsW idx u p S P κ) s v) ?_ []).pre
      fun s v h => ⟨h, by simp [rootsW], wires_nil, fun i hi => absurd hi (by simp)⟩)
    (P₂ := fun r s v => FTCtx idxBits us top pp idx u p s v ∧ LW r (rootsW idx u p S P 14) s v)
    (fun s r s' v _ _ _ hq => by simpa using hq) fun r => ?_).kEq (by simp)
  · intro κ hκ roots
    simp only [List.length_range] at hκ
    try simp only [List.getElem_range]
    try dsimp only
    refine CGood.seq (k₂ := 0) ((wire_cgood (limbs3 (S κ).1 (S κ).2 0)).pre fun _ _ _ => trivial)
      (P₂ := fun sec s v => (FTCtx idxBits us top pp idx u p s v ∧ LW roots (rootsW idx u p S P κ) s v) ∧
        sec < s.next ∧ v sec = limbs3 (S κ).1 (S κ).2 0)
      (fun s a s' v _ hp he hq => ⟨⟨hp.1.mono he, hp.2.mono he⟩, by rw [hq.2.1, hq.1]; exact Nat.lt_succ_self _,
        hq.2.2⟩) fun sec => ?_
    refine CGood.seq (k₂ := 0) ((words_cg sec).pre fun s v h => ⟨h.2.1, by rw [h.2.2]; rfl⟩)
      (P₂ := fun a s v => (FTCtx idxBits us top pp idx u p s v ∧ LW roots (rootsW idx u p S P κ) s v) ∧
        a.1 < s.next ∧ a.2.1 < s.next ∧ v a.1 = kw (S κ).1 ∧ v a.2.1 = kw (S κ).2)
      (fun s a s' v _ hp he hq => ⟨⟨hp.1.1.mono he, hp.1.2.mono he⟩, hq.1.1, hq.1.2.1,
        by rw [hq.2.1, hp.2.2]; rfl, by rw [hq.2.2.1, hp.2.2]; rfl⟩) fun a => ?_
    obtain ⟨s0, s1, sn⟩ := a
    try dsimp only
    refine CGood.seq (k₂ := 0) ((spIndexWord_cg idxBits (us.getD κ []) idx (u κ) (by omega)
        (by rw [husl κ hκ]; norm_num) (by rw [hidxl]; exact hidx) (by rw [husl κ hκ]; exact hu κ hκ)).pre
        fun s v h => ⟨h.1.1.1, h.1.1.2.1 κ hκ⟩)
      (P₂ := fun tw1 s v => ((FTCtx idxBits us top pp idx u p s v ∧ LW roots (rootsW idx u p S P κ) s v) ∧
        s0 < s.next ∧ s1 < s.next ∧ v s0 = kw (S κ).1 ∧ v s1 = kw (S κ).2) ∧
        tw1 < s.next ∧ v tw1 = kw (tw2 idx (u κ)))
      (fun s a s' v _ hp he hq => ⟨⟨⟨hp.1.1.mono he, hp.1.2.mono he⟩, lt_of_lt_of_le hp.2.1 he.next,
        lt_of_lt_of_le hp.2.2.1 he.next, hp.2.2.2⟩, hq⟩) fun tw1 => ?_
    refine CGood.seq (k₂ := 0) ((th_cg (Circuit.tweak0 9 κ 0) (sp_tw_bound 9 κ 0 (by norm_num) (by omega)
        (by norm_num)) tw1 pp [s0, s1] (by simp [hpl])).pre fun s v h => ?_)
      (P₂ := fun leaf s v => (FTCtx idxBits us top pp idx u p s v ∧ LW roots (rootsW idx u p S P κ) s v) ∧
        leaf < s.next ∧ v leaf = dVal (ftsLeafD idx u p S κ))
      (fun s a s' v _ hp he hq => ⟨⟨hp.1.1.1.mono he, hp.1.1.2.mono he⟩, hq.1, by
        rw [hq.2, sp_th_words _ _ p tw1 pp [s0, s1] v hp.2.2 hp.1.1.1.2.2.2.2]
        simp only [List.map_cons, List.map_nil, w64_kw hp.1.2.2.2.1, w64_kw hp.1.2.2.2.2]
        rfl⟩) fun leaf => ?_
    · obtain ⟨⟨⟨hc, -⟩, h0, h1, h0v, h1v⟩, htw, htwv⟩ := h
      refine ⟨fun w hw => ?_, fun w hw => ?_⟩
      · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw
        rcases hw with (rfl | hw) | rfl | rfl
        · exact htw
        · exact hc.2.2.2.2.2.1 w hw
        · exact h0
        · exact h1
      · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw
        rcases hw with (rfl | hw) | rfl | rfl
        · exact kw_isK htwv
        · exact hc.2.2.2.2.isK w hw
        · exact kw_isK h0v
        · exact kw_isK h1v
    refine CGood.seq (k₂ := 0) ((fold_cg 10 κ idxBits (us.getD κ []) top pp leaf idx (u κ) p (P κ)
        (ftsLeafD idx u p S κ) (by norm_num) (by omega) (by omega) (by rw [husl κ hκ]; norm_num)
        (by rw [hidxl]; exact hidx) (by rw [husl κ hκ]; exact hu κ hκ) hpl).pre
        fun s v h => ⟨⟨h.1.1.1, h.1.1.2.1 κ hκ, h.1.1.2.2.1, h.1.1.2.2.2.1, h.1.1.2.2.2.2⟩, h.2⟩)
      (P₂ := fun root s v => (FTCtx idxBits us top pp idx u p s v ∧ LW roots (rootsW idx u p S P κ) s v) ∧
        root < s.next ∧ ∃ Dn : Fin 4 → W, v root = dVal Dn ∧ (Dn 0, Dn 1) = rootW idx u p S P κ)
      (fun s a s' v _ hp he hq => by
        obtain ⟨hr, Dn, h1, h2⟩ := hq
        rw [husl κ hκ] at h2
        exact ⟨⟨hp.1.1.mono he, hp.1.2.mono he⟩, hr, Dn, h1, h2⟩) fun root => ?_
    refine CGood.seq (k₂ := 0) ((dToK_cgood root).pre fun s v h => h.2.1)
      (P₂ := fun rs s v => (FTCtx idxBits us top pp idx u p s v ∧ LW roots (rootsW idx u p S P κ) s v) ∧
        rs.length = 4 ∧ Wires rs s ∧ v (rs.getD 0 0) = kw (rootW idx u p S P κ).1 ∧
        v (rs.getD 1 0) = kw (rootW idx u p S P κ).2)
      (fun s rs s' v _ hp he hq => by
        obtain ⟨hc, -, Dn, hDn, hrt⟩ := hp
        refine ⟨⟨hc.1.mono he, hc.2.mono he⟩, hq.1, hq.2.1, (hq.2.2 0).trans ?_, (hq.2.2 1).trans ?_⟩
        · rw [hDn, ← hrt]; rfl
        · rw [hDn, ← hrt]; rfl) fun rs => ?_
    exact CGood.pure' fun s v _ h => ⟨_, rfl, h.1.1, by
      rw [rootsW_succ]
      exact h.1.2.append (lw2 (h.2.2.1 _ (getD_mem (by rw [h.2.1]; norm_num)))
        (h.2.2.1 _ (getD_mem (by rw [h.2.1]; norm_num))) h.2.2.2.1 h.2.2.2.2)⟩
  · try dsimp only
    refine ((CGood.hyp fun hl => th_cg (Circuit.tweak0 11 0 0)
      (sp_tw_bound 11 0 0 (by norm_num) (by norm_num) (by norm_num)) top pp r hl).pre fun s v h =>
        ⟨by rw [hpl, h.2.1, rootsW_length]; norm_num, hashPre_of h.1.2.2.1 h.1.2.2.2.1 (PPw.lw h.1.2.2.2.2) h.2⟩).weaken
      (fun _ _ h => h) ?_
    rintro s d s' v _ ⟨hc, hr⟩ _ ⟨hd, hdv⟩
    refine ⟨hd, ?_⟩
    rw [hdv, sp_th_words _ _ p top pp r v hc.2.2.2.1 hc.2.2.2.2, hr.map]

end

/-! A layer. -/

theorem block8 (a b c d e f g : W) : Rec.block [a, b, c, d, e, f, g, 0] 0 = Rec.block [a, b, c, d, e, f, g] 0 := by
  apply Vector.ext
  intro r hr
  simp only [Rec.block, Vector.getElem_ofFn, Rec.wordAt]
  interval_cases r <;> rfl

theorem layer_consts (lay : ℕ) (hlay : lay < 3) :
    Circuit.suffix (lay + 1) + Circuit.height lay = Circuit.suffix lay ∧ Circuit.suffix lay ≤ 26 ∧
      Circuit.height lay ≤ 12 := by
  interval_cases lay <;> decide

/-- Chain `i`'s end in a layer. -/
def spEnd (lay t e : ℕ) (p : Dig) (T : ℕ → Dig) (xs : List ℕ) (i : ℕ) : Dig :=
  Words.chainFrom lay t e i p (xs.getD i 0) (T i)

/-- The words of a layer's first `k` chains' ends. -/
def spEndsW (lay t e : ℕ) (p : Dig) (T : ℕ → Dig) (xs : List ℕ) (k : ℕ) : List W :=
  (List.range k).flatMap fun i => [(spEnd lay t e p T xs i).1, (spEnd lay t e p T xs i).2]

theorem spEndsW_succ (lay t e : ℕ) (p : Dig) (T : ℕ → Dig) (xs : List ℕ) (k : ℕ) :
    spEndsW lay t e p T xs (k + 1) = spEndsW lay t e p T xs k ++ [(spEnd lay t e p T xs k).1, (spEnd lay t e p T xs k).2] := by
  simp [spEndsW, List.range_succ, List.flatMap_append]

theorem spEndsW_length (lay t e : ℕ) (p : Dig) (T : ℕ → Dig) (xs : List ℕ) (k : ℕ) :
    (spEndsW lay t e p T xs k).length = 2 * k := by
  induction k with
  | zero => simp [spEndsW]
  | succ k ih => rw [spEndsW_succ, List.length_append, ih]; simp; ring

/-- A layer's chains' ends are walks of `stepHash` over the base `tweak0(1, lay, 0)` and its key word. -/
theorem spEndsW_eq (lay t e : ℕ) (p : Dig) (T : ℕ → Dig) (xs : List ℕ) (k : ℕ) :
    walkEnds (stepHash (Circuit.tweak0 1 lay 0) (tw2 t e) p.1 p.2) (fun i => xs.getD i 0) T k =
      spEndsW lay t e p T xs k := by
  obtain ⟨P0, P1⟩ := p
  simp only [walkEnds, spEndsW, spEnd, tw2, LeanVMCircuits.Sphincs.walk_stepHash]

/-- Digits below eight summing to 191 need 103 steps. -/
theorem cells_digits191 (x : List ℕ) (hlen : x.length = 42) (hlt : ∀ i < 42, x.getD i 0 < 8)
    (hsum : x.sum = 191) : (cells fun i => x.getD i 0).length = 103 := by
  rw [cells_length]
  have hx := map_range_getD x 0 42 hlen id
  rw [List.map_id] at hx
  have h1 : ∑ i ∈ Finset.range 42, x.getD i 0 = 191 := by
    rw [← sum_range_list (fun i => x.getD i 0) 42]
    exact (congrArg List.sum hx).trans hsum
  have h2 : ∑ i ∈ Finset.range 42, (7 - x.getD i 0) + ∑ i ∈ Finset.range 42, x.getD i 0 = 294 := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun i hi => show 7 - x.getD i 0 + x.getD i 0 = 7 by
      have := hlt i (Finset.mem_range.mp hi); omega]
    simp
  omega

/-- A layer's context: the parameter, zero, tweak words and the tree's and leaf's bits. -/
def LayG (pp : List ℕ) (z key top : ℕ) (tauBits eBits : List ℕ) (p : Dig) (t e : ℕ) (s : State) (v : Val) : Prop :=
  PPw pp p s v ∧ z < s.next ∧ v z = kVal 0 ∧ key < s.next ∧ v key = kw (tw2 t e) ∧ top < s.next ∧
    v top = kw (tw2 t 0) ∧ BL tauBits t s v ∧ BL eBits e s v

theorem LayG.mono {pp : List ℕ} {z key top : ℕ} {tauBits eBits : List ℕ} {p : Dig} {t e : ℕ} {s s' : State}
    {v : Val} (h : LayG pp z key top tauBits eBits p t e s v) (he : Ext s s') :
    LayG pp z key top tauBits eBits p t e s' v :=
  ⟨h.1.mono he, lt_of_lt_of_le h.2.1 he.next, h.2.2.1, lt_of_lt_of_le h.2.2.2.1 he.next, h.2.2.2.2.1,
    lt_of_lt_of_le h.2.2.2.2.2.1 he.next, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1.mono he, h.2.2.2.2.2.2.2.2.mono he⟩

section

variable {pp : List ℕ} {z key top : ℕ} {tauBits eBits : List ℕ} {p : Dig} {t e : ℕ} {s : State} {v : Val}

theorem LayG.pp' (h : LayG pp z key top tauBits eBits p t e s v) : PPw pp p s v := h.1
theorem LayG.zl (h : LayG pp z key top tauBits eBits p t e s v) : z < s.next := h.2.1
theorem LayG.zv (h : LayG pp z key top tauBits eBits p t e s v) : v z = kVal 0 := h.2.2.1
theorem LayG.keyl (h : LayG pp z key top tauBits eBits p t e s v) : key < s.next := h.2.2.2.1
theorem LayG.keyv (h : LayG pp z key top tauBits eBits p t e s v) : v key = kw (tw2 t e) := h.2.2.2.2.1
theorem LayG.topl (h : LayG pp z key top tauBits eBits p t e s v) : top < s.next := h.2.2.2.2.2.1
theorem LayG.topv (h : LayG pp z key top tauBits eBits p t e s v) : v top = kw (tw2 t 0) := h.2.2.2.2.2.2.1
theorem LayG.tau (h : LayG pp z key top tauBits eBits p t e s v) : BL tauBits t s v := h.2.2.2.2.2.2.2.1
theorem LayG.eb (h : LayG pp z key top tauBits eBits p t e s v) : BL eBits e s v := h.2.2.2.2.2.2.2.2

end

/-- A message digest's words on wires `ms`. -/
def MSw (ms : List ℕ) (M : Fin 4 → W) (s : State) (v : Val) : Prop :=
  ms.length = 4 ∧ Wires ms s ∧ v (ms.getD 0 0) = kw (M 0) ∧ v (ms.getD 1 0) = kw (M 1)

theorem MSw.mono {ms : List ℕ} {M : Fin 4 → W} {s s' : State} {v : Val} (h : MSw ms M s v) (he : Ext s s') :
    MSw ms M s' v :=
  ⟨h.1, h.2.1.mono he, h.2.2⟩

theorem kw_ofNat (n : ℕ) (h : n < 2 ^ 64) : kw (BitVec.ofNat 64 n) = kVal (ofWord n) := by
  rw [kw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

section

variable {st : ℕ → Fin 4 → K}

/-- Layer `lay` of signature `j`: its tag's rows on the bus balance, and it climbs to the root of the leaf its
chains' ends hash to. -/
theorem layer_cg (j lay : ℕ) (hlay : lay < 3) (hj : 3 * j + lay < 2 ^ 22) (idxBits pp : List ℕ) (msg idx : ℕ)
    (p : Dig) (M : Fin 4 → W) (ctrW : W) (T : ℕ → Dig) (path : ℕ → Dig) (xs : List ℕ)
    (hidxl : idxBits.length = 26) (hidx : idx < 2 ^ 26) (hpl : pp.length = 2)
    (henc : Words.encode lay (idx / 2 ^ Circuit.suffix lay)
      (idx / 2 ^ Circuit.suffix (lay + 1) % 2 ^ Circuit.height lay) p (M 0, M 1) ctrW = some xs) :
    CGood st 0 (fun s v => BL idxBits idx s v ∧ PPw pp p s v ∧ msg < s.next ∧ v msg = dVal M)
      (Circuit.layer j lay idxBits pp msg) fun _ r s' v => SigBus (3 * j + lay) 103 s' v ∧ r < s'.next ∧
        ∃ Dn : Fin 4 → W, v r = dVal Dn ∧
        (Dn 0, Dn 1) = climbP 3 lay (idx / 2 ^ Circuit.suffix lay)
          (idx / 2 ^ Circuit.suffix (lay + 1) % 2 ^ Circuit.height lay) p path
          (Words.th (Words.tweak 2 lay (idx / 2 ^ Circuit.suffix lay) 0
            (idx / 2 ^ Circuit.suffix (lay + 1) % 2 ^ Circuit.height lay)) p
            (spEndsW lay (idx / 2 ^ Circuit.suffix lay)
              (idx / 2 ^ Circuit.suffix (lay + 1) % 2 ^ Circuit.height lay) p T xs 42))
          (Circuit.height lay) := by
  obtain ⟨hsuf, hs26, hh12⟩ := layer_consts lay hlay
  set t := idx / 2 ^ Circuit.suffix lay with ht
  set e := idx / 2 ^ Circuit.suffix (lay + 1) % 2 ^ Circuit.height lay with he
  set Dfull : Fin 4 → W := digest (Rec.blake2s256 52 (Rec.block [BitVec.ofNat 64 (Circuit.tweak0 4 lay 0), tw2 t e,
    p.1, p.2, M 0, M 1, ctrW] 0) []) with hD
  have hE : ctrW.toNat < 2 ^ 32 ∧ (Dfull 0).getLsbD 63 = false ∧ (Dfull 1).getLsbD 63 = false ∧
      (Xmss.Words.digits (Dfull 0, Dfull 1)).sum = 191 ∧ xs = Xmss.Words.digits (Dfull 0, Dfull 1) := by
    unfold Words.encode at henc
    dsimp only at henc
    split_ifs at henc with hc
    exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, (Option.some.inj henc).symm⟩
  obtain ⟨hctr, h63a, h63b, hsum, rfl⟩ := hE
  set x := Xmss.Words.digits (Dfull 0, Dfull 1) with hx
  have htl : (idxBits.drop (Circuit.suffix lay)).length = 26 - Circuit.suffix lay := by
    simp only [List.length_drop, hidxl]
  have hel : ((idxBits.drop (Circuit.suffix (lay + 1))).take (Circuit.height lay)).length = Circuit.height lay := by
    simp only [List.length_take, List.length_drop, hidxl]; omega
  have htlt : t < 2 ^ (idxBits.drop (Circuit.suffix lay)).length := by
    rw [htl, ht, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show 26 - Circuit.suffix lay + Circuit.suffix lay =
      26 by omega]
    exact hidx
  have helt : e < 2 ^ ((idxBits.drop (Circuit.suffix (lay + 1))).take (Circuit.height lay)).length := by
    rw [hel, he]; exact Nat.mod_lt _ (by positivity)
  unfold Circuit.layer
  try dsimp only
  set tB := idxBits.drop (Circuit.suffix lay) with htB
  set eB := (idxBits.drop (Circuit.suffix (lay + 1))).take (Circuit.height lay) with heB
  have hBt : ∀ s v, BL idxBits idx s v → BL tB t s v := fun s v h => h.drop _
  have hBe : ∀ s v, BL idxBits idx s v → BL eB e s v := fun s v h => (h.drop _).take _
  have htw4 : Circuit.tweak0 4 lay 0 < 2 ^ 64 := sp_tw_bound 4 lay 0 (by norm_num) (by omega) (by norm_num)
  refine CGood.seq (k₂ := 0) ((kConst_cgood 0).pre (P' := fun s v => BL idxBits idx s v ∧ PPw pp p s v ∧
      msg < s.next ∧ v msg = dVal M) fun _ _ _ => trivial)
    (P₂ := fun z s v => (BL idxBits idx s v ∧ PPw pp p s v ∧ msg < s.next ∧ v msg = dVal M) ∧ z < s.next ∧
      v z = kVal 0)
    (fun s a s' v _ hp he hq => ⟨⟨hp.1.mono he, hp.2.1.mono he, lt_of_lt_of_le hp.2.2.1 he.next, hp.2.2.2⟩, hq.1,
      by rw [hq.2, ofWord_zero]⟩) fun z => ?_
  refine CGood.seq (k₂ := 0) ((spIndexWord_cg tB eB t e (by rw [htl]; omega) (by rw [hel]; omega) htlt helt).pre
      fun s v h => ⟨hBt s v h.1.1, hBe s v h.1.1⟩)
    (P₂ := fun key s v => ((BL idxBits idx s v ∧ PPw pp p s v ∧ msg < s.next ∧ v msg = dVal M) ∧ z < s.next ∧
      v z = kVal 0) ∧ key < s.next ∧ v key = kw (tw2 t e))
    (fun s a s' v _ hp he hq => ⟨⟨⟨hp.1.1.mono he, hp.1.2.1.mono he, lt_of_lt_of_le hp.1.2.2.1 he.next,
      hp.1.2.2.2⟩, lt_of_lt_of_le hp.2.1 he.next, hp.2.2⟩, hq⟩) fun key => ?_
  refine CGood.seq (k₂ := 0) ((spIndexWord_cg tB [] t 0 (by rw [htl]; omega) (by simp) htlt (by simp)).pre
      fun s v h => ⟨hBt s v h.1.1.1, wires_nil, fun i hi => absurd hi (by simp)⟩)
    (P₂ := fun top s v => LayG pp z key top tB eB p t e s v ∧ msg < s.next ∧ v msg = dVal M)
    (fun s a s' v _ hp he hq => ⟨⟨hp.1.1.2.1.mono he, lt_of_lt_of_le hp.1.2.1 he.next, hp.1.2.2,
      lt_of_lt_of_le hp.2.1 he.next, hp.2.2, hq.1, hq.2, (hBt s v hp.1.1.1).mono he, (hBe s v hp.1.1.1).mono he⟩,
      lt_of_lt_of_le hp.1.1.2.2.1 he.next, hp.1.1.2.2.2⟩) fun top => ?_
  refine CGood.seq (k₂ := 0) ((dToK_cgood msg).pre fun s v h => h.2.1)
    (P₂ := fun ms s v => LayG pp z key top tB eB p t e s v ∧ MSw ms M s v)
    (fun s ms s' v _ hp he hq => ⟨hp.1.mono he, hq.1, hq.2.1, (hq.2.2 0).trans (by rw [hp.2.2]; rfl),
      (hq.2.2 1).trans (by rw [hp.2.2]; rfl)⟩) fun ms => ?_
  refine CGood.seq (k₂ := 0) ((wire_cgood (kw ctrW)).pre fun _ _ _ => trivial)
    (P₂ := fun ctr s v => (LayG pp z key top tB eB p t e s v ∧ MSw ms M s v) ∧ ctr < s.next ∧ v ctr = kw ctrW)
    (fun s a s' v _ hp he hq => ⟨⟨hp.1.mono he, hp.2.mono he⟩, by rw [hq.2.1, hq.1]; exact Nat.lt_succ_self _,
      hq.2.2⟩) fun ctr => ?_
  refine CGood.seq (k₂ := 0) ((split_cgood ctr).pre fun s v h => ⟨h.2.1, kw_isK h.2.2⟩)
    (P₂ := fun cb s v => ((LayG pp z key top tB eB p t e s v ∧ MSw ms M s v) ∧ ctr < s.next ∧ v ctr = kw ctrW) ∧ BitsOf cb ctrW.toNat s v)
    (fun s cb s' v _ hp he hq => ⟨⟨⟨hp.1.1.mono he, hp.1.2.mono he⟩, lt_of_lt_of_le hp.2.1 he.next, hp.2.2⟩,
      hq.1, hq.2.1, fun i hi => by rw [hq.2.2 i hi, hp.2.2, toWord_kw]⟩) fun cb => ?_
  refine CGood.seq (k₂ := 0) (forIn_unit_cgood (cb.drop 32) (fun k => eqConstK k 0)
      (fun s v => ((LayG pp z key top tB eB p t e s v ∧ MSw ms M s v) ∧ ctr < s.next ∧ v ctr = kw ctrW) ∧ BitsOf cb ctrW.toNat s v)
      (fun _ _ _ h he => ⟨⟨⟨h.1.1.1.mono he, h.1.1.2.mono he⟩, lt_of_lt_of_le h.1.2.1 he.next, h.1.2.2⟩,
        h.2.mono he⟩)
      fun i hi => (eqConstK_cgood _ 0).pre fun s v h => ?_)
    (P₂ := fun _ s v => ((LayG pp z key top tB eB p t e s v ∧ MSw ms M s v) ∧ ctr < s.next ∧ v ctr = kw ctrW) ∧ BitsOf cb ctrW.toNat s v)
    (fun _ _ _ _ _ hp he _ => ⟨⟨⟨hp.1.1.1.mono he, hp.1.1.2.mono he⟩, lt_of_lt_of_le hp.1.2.1 he.next, hp.1.2.2⟩,
      hp.2.mono he⟩) fun _ => ?_
  · obtain ⟨-, hbl, hbw, hbv⟩ := h
    simp only [List.length_drop, hbl] at hi
    have hget : (cb.drop 32)[i] = cb.getD (32 + i) 0 := by
      rw [List.getElem_drop, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [hget]
    exact ⟨hbw _ (getD_mem (by omega)), by rw [hbv _ (by omega), bitK_high _ _ hctr (by omega), ofWord_zero]⟩
  refine CGood.seq (k₂ := 0) ((kConst_cgood (Circuit.tweak0 4 lay 0)).pre fun _ _ _ => trivial)
    (P₂ := fun tw0 s v => ((LayG pp z key top tB eB p t e s v ∧ MSw ms M s v) ∧ ctr < s.next ∧ v ctr = kw ctrW) ∧ tw0 < s.next ∧
      v tw0 = kw (BitVec.ofNat 64 (Circuit.tweak0 4 lay 0)))
    (fun s a s' v _ hp he hq => ⟨⟨⟨hp.1.1.1.mono he, hp.1.1.2.mono he⟩, lt_of_lt_of_le hp.1.2.1 he.next,
      hp.1.2.2⟩, hq.1, by rw [hq.2, kw_ofNat _ htw4]⟩) fun tw0 => ?_
  refine CGood.seq (k₂ := 0) ((dConst_cgood paramIVLimbs).pre fun _ _ _ => trivial)
    (P₂ := fun h s v => (((LayG pp z key top tB eB p t e s v ∧ MSw ms M s v) ∧ ctr < s.next ∧ v ctr = kw ctrW) ∧ tw0 < s.next ∧
      v tw0 = kw (BitVec.ofNat 64 (Circuit.tweak0 4 lay 0))) ∧ h < s.next ∧ v h = limbsOf paramIVLimbs)
    (fun s a s' v _ hp he hq => ⟨⟨⟨⟨hp.1.1.1.mono he, hp.1.1.2.mono he⟩, lt_of_lt_of_le hp.1.2.1 he.next,
      hp.1.2.2⟩, lt_of_lt_of_le hp.2.1 he.next, hp.2.2⟩, hq⟩) fun h => ?_
  have hmL : ∀ s v, (((LayG pp z key top tB eB p t e s v ∧ MSw ms M s v) ∧ ctr < s.next ∧ v ctr = kw ctrW) ∧ tw0 < s.next ∧
      v tw0 = kw (BitVec.ofNat 64 (Circuit.tweak0 4 lay 0))) →
      LW ([tw0, key] ++ pp ++ [ms.getD 0 0, ms.getD 1 0, ctr, z])
        ([BitVec.ofNat 64 (Circuit.tweak0 4 lay 0), tw2 t e] ++ [p.1, p.2] ++ ([M 0, M 1] ++ [ctrW, 0])) s v := by
    intro s v hh
    obtain ⟨⟨⟨hg, hms⟩, hc, hcv⟩, h0, h0v⟩ := hh
    exact ((lw2 h0 (LayG.keyl hg) h0v (LayG.keyv hg)).append (PPw.lw (LayG.pp' hg))).append
      ((lw2 (hms.2.1 _ (getD_mem (by rw [hms.1]; norm_num))) (hms.2.1 _ (getD_mem (by rw [hms.1]; norm_num)))
        hms.2.2.1 hms.2.2.2).append (lw2 hc (LayG.zl hg) hcv (by rw [LayG.zv hg, kw_zero])))
  have hm8 : ([tw0, key] ++ pp ++ [ms.getD 0 0, ms.getD 1 0, ctr, z]).length = 8 := by simp [hpl]
  refine CGood.seq (k₂ := 0) ((leafBlock_cgood h _ 52 true hm8 (by norm_num)).pre fun s v hh =>
      ⟨wires_cons.2 ⟨hh.2.1, (hmL s v hh.1).2.1⟩, fun i hi => (hmL s v hh.1).isK _ (getD_mem (by rw [hm8]; exact hi))⟩)
    (P₂ := fun d s v => LayG pp z key top tB eB p t e s v ∧ d < s.next ∧ v d = dVal Dfull)
    (fun s d s' v _ hp he hq => ⟨hp.1.1.1.1.mono he, hq.1, by
      rw [hq.2, hp.2.2, words4_paramIV, cvWords_digest, (hmL s v hp.1).map]
      simp only [List.cons_append, List.nil_append]
      rw [block8]
      rfl⟩) fun d => ?_
  refine CGood.seq (k₂ := 0) ((dToK_cgood d).pre fun s v h => h.2.1)
    (P₂ := fun ks s v => LayG pp z key top tB eB p t e s v ∧ ks.length = 4 ∧ Wires ks s ∧
      v (ks.getD 0 0) = kw (Dfull 0) ∧ v (ks.getD 1 0) = kw (Dfull 1))
    (fun s ks s' v _ hp he hq => ⟨hp.1.mono he, hq.1, hq.2.1,
      (hq.2.2 0).trans (by rw [hp.2.2]; rfl), (hq.2.2 1).trans (by rw [hp.2.2]; rfl)⟩) fun ks => ?_
  refine CGood.seq (k₂ := 0) ((split_cgood (ks.getD 0 0)).pre fun s v h =>
      ⟨h.2.2.1 _ (getD_mem (by rw [h.2.1]; norm_num)), kw_isK h.2.2.2.1⟩)
    (P₂ := fun lo s v => LayG pp z key top tB eB p t e s v ∧ ks.length = 4 ∧ Wires ks s ∧
      v (ks.getD 1 0) = kw (Dfull 1) ∧ BitsOf lo (Dfull 0).toNat s v)
    (fun s lo s' v _ hp he hq => ⟨hp.1.mono he, hp.2.1, hp.2.2.1.mono he, hp.2.2.2.2, hq.1, hq.2.1,
      fun i hi => by rw [hq.2.2 i hi, hp.2.2.2.1, toWord_kw]⟩) fun lo => ?_
  refine CGood.seq (k₂ := 0) ((split_cgood (ks.getD 1 0)).pre fun s v h =>
      ⟨h.2.2.1 _ (getD_mem (by rw [h.2.1]; norm_num)), kw_isK h.2.2.2.1⟩)
    (P₂ := fun hi s v => LayG pp z key top tB eB p t e s v ∧ BitsOf lo (Dfull 0).toNat s v ∧ BitsOf hi (Dfull 1).toNat s v)
    (fun s hi s' v _ hp he hq => ⟨hp.1.mono he, hp.2.2.2.2.mono he, hq.1, hq.2.1,
      fun i hi' => by rw [hq.2.2 i hi', hp.2.2.2.1, toWord_kw]⟩) fun hi => ?_
  have h63a' : (Dfull 0).toNat.testBit 63 = false := h63a
  have h63b' : (Dfull 1).toNat.testBit 63 = false := h63b
  refine CGood.seq (k₂ := 0) ((eqConstK_cgood (lo.getD 63 0) 0).pre fun s v h =>
      ⟨h.2.1.2.1 _ (getD_mem (by rw [h.2.1.1]; norm_num)),
        by rw [h.2.1.2.2 63 (by norm_num), bitK_eq, h63a', ofWord_zero]; rfl⟩)
    (P₂ := fun _ s v => LayG pp z key top tB eB p t e s v ∧ BitsOf lo (Dfull 0).toNat s v ∧ BitsOf hi (Dfull 1).toNat s v)
    (fun s _ s' v _ hp he hq => ⟨hp.1.mono he, hp.2.1.mono he, hp.2.2.mono he⟩) fun _ => ?_
  refine CGood.seq (k₂ := 0) ((eqConstK_cgood (hi.getD 63 0) 0).pre fun s v h =>
      ⟨h.2.2.2.1 _ (getD_mem (by rw [h.2.2.1]; norm_num)),
        by rw [h.2.2.2.2 63 (by norm_num), bitK_eq, h63b', ofWord_zero]; rfl⟩)
    (P₂ := fun _ s v => LayG pp z key top tB eB p t e s v ∧ BitsOf lo (Dfull 0).toNat s v ∧ BitsOf hi (Dfull 1).toNat s v)
    (fun s _ s' v _ hp he hq => ⟨hp.1.mono he, hp.2.1.mono he, hp.2.2.mono he⟩) fun _ => ?_
  try dsimp only
  refine CGood.seq (k₂ := 0) ((digitProduct_cg (List.take 63 lo ++ List.take 63 hi) (bitsB Dfull)).pre
      fun s v h => dbits_of lo hi Dfull s v h.2.1 h.2.2)
    (P₂ := fun prod s v => LayG pp z key top tB eB p t e s v ∧ DBits (List.take 63 lo ++ List.take 63 hi) (bitsB Dfull) s v ∧ prod < s.next ∧ v prod = eVal (emb (root ^ psum (bitsB Dfull) 42)))
    (fun s prod s' v _ hp he hq => ⟨hp.1.mono he, dbits_of lo hi Dfull s' v (hp.2.1.mono he) (hp.2.2.mono he),
      hq.1, hq.2⟩) fun prod => ?_
  refine CGood.seq (k₂ := 0) ((eqConstE_cgood prod Circuit.targetWord 0 0).pre fun s v h =>
      ⟨h.2.2.1, by rw [h.2.2.2, psum_eq, hsum, ofWord_zero, toE_emb, target_eq]⟩)
    (P₂ := fun _ s v => LayG pp z key top tB eB p t e s v ∧ DBits (List.take 63 lo ++ List.take 63 hi) (bitsB Dfull) s v)
    (fun s _ s' v _ hp he hq => ⟨hp.1.mono he, hp.2.1.mono he⟩) fun _ => ?_
  try dsimp only
  have hxd : ∀ i < 42, dig (bitsB Dfull) i 3 = x.getD i 0 := fun i hi => (digits_getD Dfull i hi).symm
  have hcells : (cells fun i => x.getD i 0).length = 103 :=
    cells_digits191 x (by rw [hx]; simp [Xmss.Words.digits]) (fun i hi => by
      rw [← hxd i hi, dig_three]
      split_ifs <;> omega) hsum
  refine CGood.seq (k₂ := 0) ((chains_cg (Circuit.tweak0 1 lay 0) (3 * j + lay) 103
      (by unfold Circuit.tweak0; omega) hj key pp (List.take 63 lo ++ List.take 63 hi)
      (tw2 t e) p T (bitsB Dfull) x hxd hcells).pre
      fun s v h => ⟨LayG.keyl h.1, LayG.keyv h.1, LayG.pp' h.1, h.2⟩)
    (P₂ := fun ends s v => LayG pp z key top tB eB p t e s v ∧ LW ends (spEndsW lay t e p T x 42) s v ∧
      SigBus (3 * j + lay) 103 s v)
    (fun s ends s' v _ hp he hq => ⟨hp.1.mono he, by rw [← spEndsW_eq]; exact hq.1, hq.2⟩) fun ends => ?_
  refine CGood.seq (k₂ := 0) ((CGood.hyp fun hl => th_cg (Circuit.tweak0 2 lay 0)
      (sp_tw_bound 2 lay 0 (by norm_num) (by omega) (by norm_num)) key pp ends hl).pre fun s v h => ⟨by
        rw [hpl, h.2.1.1, spEndsW_length]; norm_num,
        hashPre_of (LayG.keyl h.1) (LayG.keyv h.1) (PPw.lw (LayG.pp' h.1)) h.2.1⟩)
    (P₂ := fun leaf s v => LayG pp z key top tB eB p t e s v ∧ leaf < s.next ∧ v leaf = dVal (digest (hashWords
      ([BitVec.ofNat 64 (Circuit.tweak0 2 lay 0), tw2 t e, p.1, p.2] ++ spEndsW lay t e p T x 42))) ∧
      SigBus (3 * j + lay) 103 s v)
    (fun s leaf s' v _ hp he hq => ⟨hp.1.mono he, hq.1, by
      rw [hq.2, sp_th_words _ _ p key pp ends v (LayG.keyv hp.1) (LayG.pp' hp.1), hp.2.1.map],
      hp.2.2.mono he⟩) fun leaf => ?_
  refine ((fold_cg 3 lay tB eB top pp leaf t e p path _ (by norm_num) (by omega) (by rw [htl]; omega)
      (by rw [hel]; omega) htlt helt hpl).pre fun s v h =>
        ⟨⟨LayG.tau h.1, LayG.eb h.1, LayG.topl h.1, LayG.topv h.1, LayG.pp' h.1⟩, h.2.1, h.2.2.1⟩).weaken
    (fun _ _ h => h) ?_
  rintro s r s' v _ hP he ⟨hr, Dn, h1, h2⟩
  refine ⟨hP.2.2.2.mono he, hr, Dn, h1, ?_⟩
  rw [h2, hel]
  rfl

end

/-! The signature's words. -/

/-- A signature's few-time secret `κ`, zero past 14. -/
def secN (sig : Words.Sig) (κ : ℕ) : Dig := if h : κ < 14 then sig.secrets ⟨κ, h⟩ else (0, 0)

/-- A few-time path's sibling `l`. -/
def ftsPathN (sig : Words.Sig) (κ l : ℕ) : Dig :=
  if h : κ < 14 ∧ l < 10 then sig.ftsPaths ⟨κ, h.1⟩ ⟨l, h.2⟩ else (0, 0)

/-- Layer `lay`'s chain element `i`. -/
def tipL (sig : Words.Sig) (lay : ℕ) (hlay : lay < 3) (i : ℕ) : Dig :=
  if h : i < 42 then sig.tips ⟨lay, hlay⟩ ⟨i, h⟩ else (0, 0)

/-- Layer `lay`'s path sibling `l`. -/
def pathL (sig : Words.Sig) (lay : ℕ) (hlay : lay < 3) (l : ℕ) : Dig :=
  if h : l < Circuit.height lay then sig.paths ⟨lay, hlay⟩ ⟨l, h⟩ else (0, 0)

theorem fts_key_eq (idx : ℕ) (u : ℕ → ℕ) (pp : Dig) (sig : Words.Sig) :
    ((List.ofFn fun κ : Fin 14 => Words.ftsRoot idx κ (u κ) pp (sig.secrets κ) (sig.ftsPaths κ)).flatMap
      fun d => [d.1, d.2]) = rootsW idx u pp (secN sig) (ftsPathN sig) 14 := by
  have h : (List.ofFn fun κ : Fin 14 => Words.ftsRoot idx κ (u κ) pp (sig.secrets κ) (sig.ftsPaths κ)) =
      List.ofFn fun κ : Fin 14 => rootW idx u pp (secN sig) (ftsPathN sig) κ.val := by
    refine congrArg List.ofFn (funext fun κ => ?_)
    have hleaf : Words.th (Words.tweak 9 κ idx 0 (u κ)) pp [(sig.secrets κ).1, (sig.secrets κ).2] =
        (ftsLeafD idx u pp (secN sig) κ 0, ftsLeafD idx u pp (secN sig) κ 1) := by
      simp only [ftsLeafD, secN, dif_pos κ.isLt]
      exact (sp_dVal_th _ _ _).symm
    rw [Words.ftsRoot, climb_eq' 10 κ idx (u κ) 10 pp (sig.ftsPaths κ) (ftsPathN sig κ)
      (fun l hl => by simp [ftsPathN, κ.isLt, hl]), hleaf]
    rfl
  rw [h, ofFn_eq_range, List.flatMap_map]
  rfl

theorem layer_word (pp : Dig) (idx : ℕ) (sig : Words.Sig) (Rin R : Dig) (lay : ℕ) (hlay : lay < 3)
    (h : Words.layerRoot pp idx sig Rin ⟨lay, hlay⟩ = some R) :
    ∃ xs, Words.encode lay (idx / 2 ^ Circuit.suffix lay) (idx / 2 ^ Circuit.suffix (lay + 1) % 2 ^ Circuit.height lay)
        pp Rin (sig.counters ⟨lay, hlay⟩) = some xs ∧
      R = climbP 3 lay (idx / 2 ^ Circuit.suffix lay) (idx / 2 ^ Circuit.suffix (lay + 1) % 2 ^ Circuit.height lay)
        pp (pathL sig lay hlay) (Words.th (Words.tweak 2 lay (idx / 2 ^ Circuit.suffix lay) 0
          (idx / 2 ^ Circuit.suffix (lay + 1) % 2 ^ Circuit.height lay)) pp
          (spEndsW lay (idx / 2 ^ Circuit.suffix lay) (idx / 2 ^ Circuit.suffix (lay + 1) % 2 ^ Circuit.height lay)
            pp (tipL sig lay hlay) xs 42)) (Circuit.height lay) := by
  unfold Words.layerRoot at h
  dsimp only at h
  cases he : Words.encode lay (idx / 2 ^ Circuit.suffix lay)
      (idx / 2 ^ Circuit.suffix (lay + 1) % 2 ^ Circuit.height lay) pp Rin (sig.counters ⟨lay, hlay⟩) with
  | none =>
    simp only [Words.tau, Words.leafIndex, Words.height] at h
    rw [he] at h
    simp at h
  | some xs =>
    simp only [Words.tau, Words.leafIndex, Words.height] at h
    rw [he] at h
    dsimp only at h
    refine ⟨xs, rfl, ?_⟩
    rw [← Option.some.inj h, climb_eq' 3 lay _ _ (Circuit.height lay) pp
      (sig.paths ⟨lay, hlay⟩ : Fin (Circuit.height lay) → Dig) (pathL sig lay hlay)
      (fun l hl => by rw [pathL, dif_pos hl]; rfl)]
    have h2 : (List.ofFn fun i : Fin 42 => Words.chainFrom lay (idx / 2 ^ Circuit.suffix lay)
        (idx / 2 ^ Circuit.suffix (lay + 1) % 2 ^ Circuit.height lay) i pp (xs.getD i 0) (sig.tips ⟨lay, hlay⟩ i)) =
        List.ofFn fun i : Fin 42 => spEnd lay (idx / 2 ^ Circuit.suffix lay)
          (idx / 2 ^ Circuit.suffix (lay + 1) % 2 ^ Circuit.height lay) pp (tipL sig lay hlay) xs i.val := by
      refine congrArg List.ofFn (funext fun i => ?_)
      simp [spEnd, tipL, i.isLt]
    rw [Words.otsLeaf, h2, ofFn_eq_range, List.flatMap_map]
    rfl

theorem BL.congr {bs : List ℕ} {n n' : ℕ} {s : State} {v : Val} (h : BL bs n s v) (hn : n = n') : BL bs n' s v :=
  hn ▸ h

theorem us_getD' (bits : List ℕ) (κ : ℕ) (hκ : κ < 15) :
    (((List.range 15).map fun k => (bits.drop (26 + 10 * k)).take 10).getD κ []) =
      (bits.drop (26 + 10 * κ)).take 10 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hκ]
  rfl

section

variable {st : ℕ → Fin 4 → K}

/-- Layer `lay`'s step of signature `j`'s loop: the message it signs reaches the next, and its tag's rows on the bus
balance. -/
theorem layer_step (j lay : ℕ) (hlay : lay < 3) (hj : 3 * j + lay < 2 ^ 22) (idxBits pp : List ℕ) (msg idx : ℕ)
    (p : Dig) (sig : Words.Sig) (Rin Rout : Dig) (G : State → Val → Prop) (hG : ∀ s s' v, G s v → Ext s s' → G s' v)
    (hGb : ∀ s v, G s v → BL idxBits idx s v ∧ PPw pp p s v)
    (hidxl : idxBits.length = 26) (hidx : idx < 2 ^ 26) (hpl : pp.length = 2)
    (hlr : Words.layerRoot p idx sig Rin ⟨lay, hlay⟩ = some Rout) :
    CGood st 0 (fun s v => G s v ∧ msg < s.next ∧ ∃ Dn : Fin 4 → W, v msg = dVal Dn ∧ (Dn 0, Dn 1) = Rin)
      (do
        let node ← Circuit.layer j lay idxBits pp msg
        pure (ForInStep.yield node))
      fun _ r s' v => ∃ b', r = ForInStep.yield b' ∧ (G s' v ∧ SigBus (3 * j + lay) 103 s' v) ∧ b' < s'.next ∧
        ∃ Dn : Fin 4 → W, v b' = dVal Dn ∧ (Dn 0, Dn 1) = Rout := by
  obtain ⟨xs, henc, hR⟩ := layer_word p idx sig Rin Rout lay hlay hlr
  apply CGood.intro
  intro s₀ val₀
  have hM : ∀ s v, s = s₀ → Agree s.next val₀ v → msg < s.next →
      ∀ Dn : Fin 4 → W, v msg = dVal Dn → words4 (val₀ msg) = Dn := by
    intro s v hs hag hm Dn hDn
    rw [← hag msg hm, hDn, words4_dVal]
  by_cases hmv : ∃ Dn : Fin 4 → W, val₀ msg = dVal Dn ∧ (Dn 0, Dn 1) = Rin
  · obtain ⟨D0, hD0, hD0R⟩ := hmv
    have hw : words4 (val₀ msg) = D0 := by rw [hD0, words4_dVal]
    refine CGood.seq (k₂ := 0) ((layer_cg j lay hlay hj idxBits pp msg idx p (words4 (val₀ msg))
        (sig.counters ⟨lay, hlay⟩) (tipL sig lay hlay) (pathL sig lay hlay) xs hidxl hidx hpl
        (by rw [hw, hD0R]; exact henc)).pre fun s v h => ?_)
      (P₂ := fun r s v => (G s v ∧ SigBus (3 * j + lay) 103 s v) ∧ r < s.next ∧
        ∃ Dn : Fin 4 → W, v r = dVal Dn ∧ (Dn 0, Dn 1) = Rout)
      (fun s r s' v _ hp he hq => ⟨⟨hG _ _ _ hp.2.2.1 he, hq.1⟩, hq.2.1, by
        obtain ⟨Dn, h1, h2⟩ := hq.2.2
        refine ⟨Dn, h1, ?_⟩
        rw [h2, hR]⟩) fun r => ?_
    · obtain ⟨hs, hag, hg, hm, Dn, hDn, -⟩ := h
      refine ⟨(hGb s v hg).1, (hGb s v hg).2, hm, ?_⟩
      rw [hM s v hs hag hm Dn hDn, hDn]
    · exact CGood.pure' fun s v _ h => ⟨r, rfl, h⟩
  · intro s val hi hc hsat hP
    obtain ⟨hs, hag, -, hm, Dn, hDn, hDR⟩ := hP val (Agree.refl _ _)
    subst hs
    exact absurd ⟨Dn, by rw [← hag msg hm]; exact hDn, hDR⟩ hmv

end

section

variable {st : ℕ → Fin 4 → K}

/-- The signature's statement words. -/
def SH4 (rt p : Dig) (m : W × W × W × W) (root pp mlo mhi : List ℕ) (s : State) (v : Val) : Prop :=
  LW root [rt.1, rt.2] s v ∧ LW pp [p.1, p.2] s v ∧ LW mlo [m.1, m.2.1] s v ∧ LW mhi [m.2.2.1, m.2.2.2] s v

theorem SH4.mono {rt p : Dig} {m : W × W × W × W} {root pp mlo mhi : List ℕ} {s s' : State} {v : Val}
    (h : SH4 rt p m root pp mlo mhi s v) (he : Ext s s') : SH4 rt p m root pp mlo mhi s' v :=
  ⟨h.1.mono he, h.2.1.mono he, h.2.2.1.mono he, h.2.2.2.mono he⟩

/-- The signature's context after the message digest's bits. -/
def SG (rt p : Dig) (m : W × W × W × W) (root pp mlo mhi : List ℕ) (z : ℕ) (w0 w1 w2 : List ℕ) (V : ℕ)
    (s : State) (v : Val) : Prop :=
  SH4 rt p m root pp mlo mhi s v ∧ z < s.next ∧ v z = kVal 0 ∧
    (w0.length = 64 ∧ w1.length = 64 ∧ w2.length = 64) ∧ BL (w0 ++ w1 ++ w2) V s v

theorem SG.mono {rt p : Dig} {m : W × W × W × W} {root pp mlo mhi : List ℕ} {z : ℕ} {w0 w1 w2 : List ℕ} {V : ℕ}
    {s s' : State} {v : Val} (h : SG rt p m root pp mlo mhi z w0 w1 w2 V s v) (he : Ext s s') :
    SG rt p m root pp mlo mhi z w0 w1 w2 V s' v :=
  ⟨h.1.mono he, lt_of_lt_of_le h.2.1 he.next, h.2.2.1, h.2.2.2.1, h.2.2.2.2.mono he⟩

/-- Signature `j`'s layers from layer `3 - k` up have their tags' rows on the bus. -/
def LayBus (j k : ℕ) (s : State) (v : Val) : Prop := ∀ lay < 3, 3 ≤ lay + k → SigBus (3 * j + lay) 103 s v

theorem LayBus.mono {j k : ℕ} {s s' : State} {v : Val} (h : LayBus j k s v) (he : Ext s s') : LayBus j k s' v :=
  fun lay hl hk => (h lay hl hk).mono he

/-- Signature `j < 2^20`, verifying, keeps its statement words and its layers' tags' rows on the bus balance. -/
theorem signature_cg (j : ℕ) (hj : j < 2 ^ 20) (rt p : Dig) (m : W × W × W × W) (sig : Words.Sig)
    (henc : Encodes st j rt p m) (hver : Words.verify rt p m sig = true) :
    CGood st 4 (fun s _ => s.statement = 4 * j) (Circuit.signature j) fun _ _ s' v =>
      ∀ lay < 3, SigBus (3 * j + lay) 103 s' v := by
  obtain ⟨h0, h1, h2, h3⟩ := henc
  set Dm : Fin 4 → W := digest (hashWords [(Words.tweak 12 0 0 0 0).1, (Words.tweak 12 0 0 0 0).2, p.1, p.2,
    sig.rho.1, sig.rho.2, rt.1, rt.2, m.1, m.2.1, m.2.2.1, m.2.2.2]) with hDm
  set V := (Dm 0).toNat + 2 ^ 64 * (Dm 1).toNat + 2 ^ 128 * (Dm 2).toNat with hV
  set idx := V % 2 ^ 26 with hidxd
  set u : ℕ → ℕ := fun κ => V / 2 ^ (26 + 10 * κ) % 2 ^ 10 with hud
  have hmd : Words.messageDigest p rt sig.rho m = (idx, u) := rfl
  set key := Words.th (Words.tweak 11 0 idx 0 0) p ((List.ofFn fun kappa : Fin 14 =>
    Words.ftsRoot idx kappa (u kappa) p (sig.secrets kappa) (sig.ftsPaths kappa)).flatMap fun d => [d.1, d.2])
    with hkey
  have hv2 : u 14 = 0 ∧ ∃ top, [2, 1, 0].foldlM (Words.layerRoot p idx sig) key = some top ∧ top = rt := by
    unfold Words.verify at hver
    rw [hmd] at hver
    dsimp only at hver
    have hu : u 14 = 0 := by
      by_contra hu'
      rw [if_pos hu'] at hver
      exact Bool.false_ne_true hver
    rw [if_neg (fun h => h hu)] at hver
    cases hf : [2, 1, 0].foldlM (Words.layerRoot p idx sig) key with
    | none => rw [hf] at hver; exact absurd hver Bool.false_ne_true
    | some top =>
      rw [hf] at hver
      exact ⟨hu, top, rfl, beq_iff_eq.mp hver⟩
  obtain ⟨hu14, top, hf, htop⟩ := hv2
  rw [htop] at hf
  have hl : ∃ r1 r2, Words.layerRoot p idx sig key ⟨2, by norm_num⟩ = some r1 ∧
      Words.layerRoot p idx sig r1 ⟨1, by norm_num⟩ = some r2 ∧ Words.layerRoot p idx sig r2 ⟨0, by norm_num⟩ = some rt := by
    cases h2 : Words.layerRoot p idx sig key 2 with
    | none => simp [List.foldlM, h2] at hf
    | some r1 =>
      cases h1 : Words.layerRoot p idx sig r1 1 with
      | none => simp [List.foldlM, h2, h1] at hf
      | some r2 =>
        refine ⟨r1, r2, h2, h1, ?_⟩
        simpa [List.foldlM, h2, h1] using hf
  obtain ⟨r1, r2, hl2, hl1, hl0⟩ := hl
  have hidx : idx < 2 ^ 26 := Nat.mod_lt _ (by positivity)
  have hu : ∀ κ < 14, u κ < 2 ^ 10 := fun κ _ => Nat.mod_lt _ (by positivity)
  set Kd : Fin 4 → W := digest (hashWords ([BitVec.ofNat 64 (Circuit.tweak0 11 0 0), tw2 idx 0, p.1, p.2] ++
    rootsW idx u p (secN sig) (ftsPathN sig) 14)) with hKdd
  have hKd : (Kd 0, Kd 1) = key := by
    rw [hkey, fts_key_eq, tweak_eq, hKdd]
    exact sp_dVal_th (BitVec.ofNat 64 (Circuit.tweak0 11 0 0), tw2 idx 0) p (rootsW idx u p (secN sig) (ftsPathN sig) 14)
  unfold Circuit.signature
  refine CGood.seq (k₂ := 3) ((statementWords_cg 1 rt.1 rt.2 0 (Or.inl ⟨rfl, rfl⟩)).stmt.pre
      fun s _ h => by rw [h]; exact h0)
    (P₂ := fun root s v => s.statement = 4 * j + 1 ∧ LW root [rt.1, rt.2] s v)
    (fun s a s' v _ hp he hq => ⟨by rw [hq.2, hp], sw_lw1 hq.1⟩) fun root => ?_
  refine CGood.seq (k₂ := 2) ((statementWords_cg 1 p.1 p.2 0 (Or.inl ⟨rfl, rfl⟩)).stmt.pre
      fun s _ h => by rw [h.1]; exact h1)
    (P₂ := fun pp s v => s.statement = 4 * j + 2 ∧ LW root [rt.1, rt.2] s v ∧ LW pp [p.1, p.2] s v)
    (fun s a s' v _ hp he hq => ⟨by rw [hq.2, hp.1], hp.2.mono he, sw_lw1 hq.1⟩) fun pp => ?_
  refine CGood.seq (k₂ := 1) ((statementWords_cg 1 m.1 m.2.1 0 (Or.inl ⟨rfl, rfl⟩)).stmt.pre
      fun s _ h => by rw [h.1]; exact h2)
    (P₂ := fun mlo s v => s.statement = 4 * j + 3 ∧ LW root [rt.1, rt.2] s v ∧ LW pp [p.1, p.2] s v ∧
      LW mlo [m.1, m.2.1] s v)
    (fun s a s' v _ hp he hq => ⟨by rw [hq.2, hp.1], hp.2.1.mono he, hp.2.2.mono he, sw_lw1 hq.1⟩) fun mlo => ?_
  refine CGood.seq (k₂ := 0) ((statementWords_cg 1 m.2.2.1 m.2.2.2 0 (Or.inl ⟨rfl, rfl⟩)).stmt.pre
      fun s _ h => by rw [h.1]; exact h3)
    (P₂ := fun mhi s v => SH4 rt p m root pp mlo mhi s v)
    (fun s a s' v _ hp he hq => ⟨hp.2.1.mono he, hp.2.2.1.mono he, hp.2.2.2.mono he, sw_lw1 hq.1⟩) fun mhi => ?_
  refine CGood.seq (k₂ := 0) ((kConst_cgood 0).pre fun _ _ _ => trivial)
    (P₂ := fun z s v => SH4 rt p m root pp mlo mhi s v ∧ z < s.next ∧ v z = kVal 0)
    (fun s a s' v _ hp he hq => ⟨hp.mono he, hq.1, by rw [hq.2, ofWord_zero]⟩) fun z => ?_
  refine CGood.seq (k₂ := 0) ((wire_cgood (limbs3 sig.rho.1 sig.rho.2 0)).pre fun _ _ _ => trivial)
    (P₂ := fun rho s v => (SH4 rt p m root pp mlo mhi s v ∧ z < s.next ∧ v z = kVal 0) ∧ rho < s.next ∧ v rho = limbs3 sig.rho.1 sig.rho.2 0)
    (fun s a s' v _ hp he hq => ⟨⟨hp.1.mono he, lt_of_lt_of_le hp.2.1 he.next, hp.2.2⟩,
      by rw [hq.2.1, hq.1]; exact Nat.lt_succ_self _, hq.2.2⟩) fun rho => ?_
  refine CGood.seq (k₂ := 0) ((words_cg rho).pre fun s v h => ⟨h.2.1, by rw [h.2.2]; rfl⟩)
    (P₂ := fun a s v => (SH4 rt p m root pp mlo mhi s v ∧ z < s.next ∧ v z = kVal 0) ∧ LW [a.1, a.2.1] [sig.rho.1, sig.rho.2] s v)
    (fun s a s' v _ hp he hq => ⟨⟨hp.1.1.mono he, lt_of_lt_of_le hp.1.2.1 he.next, hp.1.2.2⟩,
      lw2 hq.1.1 hq.1.2.1 (by rw [hq.2.1, hp.2.2]; rfl) (by rw [hq.2.2.1, hp.2.2]; rfl)⟩) fun a => ?_
  obtain ⟨r0, r1', sn⟩ := a
  try dsimp only
  have hpl : ∀ s v, (SH4 rt p m root pp mlo mhi s v ∧ z < s.next ∧ v z = kVal 0) ∧ LW [r0, r1'] [sig.rho.1, sig.rho.2] s v →
      LW ([r0, r1'] ++ root ++ mlo ++ mhi) ([sig.rho.1, sig.rho.2] ++ [rt.1, rt.2] ++ [m.1, m.2.1] ++
        [m.2.2.1, m.2.2.2]) s v := fun s v h =>
    ((h.2.append h.1.1.1).append h.1.1.2.2.1).append h.1.1.2.2.2
  refine CGood.seq (k₂ := 0) ((CGood.hyp fun hl => th_cg (Circuit.tweak0 12 0 0)
      (sp_tw_bound 12 0 0 (by norm_num) (by norm_num) (by norm_num)) z pp ([r0, r1'] ++ root ++ mlo ++ mhi) hl).pre
      fun s v h => ⟨by rw [h.1.1.2.1.1, (hpl s v h).1]; norm_num,
        hashPre_of (t := tw2 0 0) h.1.2.1 (by rw [h.1.2.2, tw2_zero, kw_zero]) h.1.1.2.1 (hpl s v h)⟩)
    (P₂ := fun d s v => (SH4 rt p m root pp mlo mhi s v ∧ z < s.next ∧ v z = kVal 0) ∧ d < s.next ∧ v d = dVal Dm)
    (fun s d s' v _ hp he hq => ⟨⟨hp.1.1.mono he, lt_of_lt_of_le hp.1.2.1 he.next, hp.1.2.2⟩, hq.1, by
      rw [hq.2, sp_th_words _ (tw2 0 0) p z pp _ v (by rw [hp.1.2.2, tw2_zero, kw_zero]) hp.1.1.2.1.ppw,
        (hpl s v hp).map, hDm, tweak_eq]
      simp only [List.cons_append, List.nil_append]⟩) fun d => ?_
  refine CGood.seq (k₂ := 0) ((dToK_cgood d).pre fun s v h => h.2.1)
    (P₂ := fun ks s v => (SH4 rt p m root pp mlo mhi s v ∧ z < s.next ∧ v z = kVal 0) ∧ ks.length = 4 ∧ Wires ks s ∧
      v (ks.getD 0 0) = kw (Dm 0) ∧ v (ks.getD 1 0) = kw (Dm 1) ∧ v (ks.getD 2 0) = kw (Dm 2))
    (fun s ks s' v _ hp he hq => ⟨⟨hp.1.1.mono he, lt_of_lt_of_le hp.1.2.1 he.next, hp.1.2.2⟩, hq.1, hq.2.1,
      (hq.2.2 0).trans (by rw [hp.2.2]; rfl), (hq.2.2 1).trans (by rw [hp.2.2]; rfl),
      (hq.2.2 2).trans (by rw [hp.2.2]; rfl)⟩) fun ks => ?_
  refine CGood.seq (k₂ := 0) ((split_cgood (ks.getD 0 0)).pre fun s v h =>
      ⟨h.2.2.1 _ (getD_mem (by rw [h.2.1]; norm_num)), kw_isK h.2.2.2.1⟩)
    (P₂ := fun w0 s v => ((SH4 rt p m root pp mlo mhi s v ∧ z < s.next ∧ v z = kVal 0) ∧ ks.length = 4 ∧ Wires ks s ∧
      v (ks.getD 0 0) = kw (Dm 0) ∧ v (ks.getD 1 0) = kw (Dm 1) ∧ v (ks.getD 2 0) = kw (Dm 2)) ∧
      BitsOf w0 (Dm 0).toNat s v)
    (fun s w s' v _ hp he hq => ⟨⟨⟨hp.1.1.mono he, lt_of_lt_of_le hp.1.2.1 he.next, hp.1.2.2⟩, hp.2.1,
      hp.2.2.1.mono he, hp.2.2.2⟩, hq.1, hq.2.1, fun i hi => by rw [hq.2.2 i hi, hp.2.2.2.1, toWord_kw]⟩)
    fun w0 => ?_
  refine CGood.seq (k₂ := 0) ((split_cgood (ks.getD 1 0)).pre fun s v h =>
      ⟨h.1.2.2.1 _ (getD_mem (by rw [h.1.2.1]; norm_num)), kw_isK h.1.2.2.2.2.1⟩)
    (P₂ := fun w1 s v => (((SH4 rt p m root pp mlo mhi s v ∧ z < s.next ∧ v z = kVal 0) ∧ ks.length = 4 ∧ Wires ks s ∧
      v (ks.getD 0 0) = kw (Dm 0) ∧ v (ks.getD 1 0) = kw (Dm 1) ∧ v (ks.getD 2 0) = kw (Dm 2)) ∧
      BitsOf w0 (Dm 0).toNat s v) ∧ BitsOf w1 (Dm 1).toNat s v)
    (fun s w s' v _ hp he hq => ⟨⟨⟨⟨hp.1.1.1.mono he, lt_of_lt_of_le hp.1.1.2.1 he.next, hp.1.1.2.2⟩,
      hp.1.2.1, hp.1.2.2.1.mono he, hp.1.2.2.2⟩, hp.2.mono he⟩, hq.1, hq.2.1,
      fun i hi => by rw [hq.2.2 i hi, hp.1.2.2.2.2.1, toWord_kw]⟩) fun w1 => ?_
  refine CGood.seq (k₂ := 0) ((split_cgood (ks.getD 2 0)).pre fun s v h =>
      ⟨h.1.1.2.2.1 _ (getD_mem (by rw [h.1.1.2.1]; norm_num)), kw_isK h.1.1.2.2.2.2.2⟩)
    (P₂ := fun w2 s v => SG rt p m root pp mlo mhi z w0 w1 w2 V s v)
    (fun s w s' v _ hp he hq => by
      obtain ⟨⟨⟨hg, -, -, -, -, h2v⟩, hb0⟩, hb1⟩ := hp
      have hb2 : BitsOf w (Dm 2).toNat s' v := ⟨hq.1, hq.2.1, fun i hi => by rw [hq.2.2 i hi, h2v, toWord_kw]⟩
      have h01 := (BL.of_bitsOf (hb0.mono he)).append (BL.of_bitsOf (hb1.mono he)) (by rw [hb0.1]; exact (Dm 0).isLt)
      have h012 := h01.append (BL.of_bitsOf hb2) (by
        rw [List.length_append, hb0.1, hb1.1]
        have := (Dm 0).isLt; have := (Dm 1).isLt
        calc (Dm 0).toNat + (Dm 1).toNat * 2 ^ 64 < 2 ^ 64 + (Dm 1).toNat * 2 ^ 64 := by omega
          _ = ((Dm 1).toNat + 1) * 2 ^ 64 := by ring
          _ ≤ 2 ^ 64 * 2 ^ 64 := Nat.mul_le_mul_right _ (by omega)
          _ = 2 ^ (64 + 64) := by norm_num)
      refine ⟨hg.1.mono he, lt_of_lt_of_le hg.2.1 he.next, hg.2.2, ⟨hb0.1, hb1.1, hq.1⟩, h012.congr ?_⟩
      rw [List.length_append, hb0.1, hb1.1, hV]
      ring) fun w2 => ?_
  try dsimp only
  have hidxBL : ∀ s v, SG rt p m root pp mlo mhi z w0 w1 w2 V s v → BL ((w0 ++ w1 ++ w2).take 26) idx s v := fun s v h => h.2.2.2.2.take 26
  have huBL : ∀ s v, SG rt p m root pp mlo mhi z w0 w1 w2 V s v → ∀ κ < 15, BL (((List.range 15).map fun k => ((w0 ++ w1 ++ w2).drop (26 + 10 * k)).take 10).getD κ []) (u κ) s v := by
    intro s v h κ hκ
    rw [us_getD' _ κ hκ]
    exact (h.2.2.2.2.drop _).take 10
  have hlen : ∀ s v, SG rt p m root pp mlo mhi z w0 w1 w2 V s v → (w0 ++ w1 ++ w2).length = 192 := fun s v h => by
    rw [List.length_append, List.length_append, h.2.2.2.1.1, h.2.2.2.1.2.1, h.2.2.2.1.2.2]
  refine CGood.seq (k₂ := 0) (forIn_unit_cgood _ (fun k => eqConstK k 0) (fun s v => SG rt p m root pp mlo mhi z w0 w1 w2 V s v)
      (fun _ _ _ h he => h.mono he) fun i hi => (eqConstK_cgood _ 0).pre fun s v h => ?_)
    (P₂ := fun _ s v => SG rt p m root pp mlo mhi z w0 w1 w2 V s v) (fun _ _ _ _ _ hp he _ => hp.mono he) fun _ => ?_
  · have hb := huBL s v h 14 (by norm_num)
    rw [getElem_eq_getD]
    refine ⟨hb.1 _ (getD_mem hi), ?_⟩
    rw [hb.2 i hi, hu14, bitK, Nat.zero_testBit, ofWord_zero]
    rfl
  refine CGood.seq (k₂ := 0) ((CGood.hyp fun (hl : ((w0 ++ w1 ++ w2).take 26).length = 26) => spIndexWord_cg ((w0 ++ w1 ++ w2).take 26) [] idx 0 (by omega)
      (by simp) (by rw [hl]; exact hidx) (by simp)).pre fun s v h =>
        ⟨by simp only [List.length_take, hlen s v h]; norm_num, hidxBL s v h, wires_nil, fun i hi => absurd hi (by simp)⟩)
    (P₂ := fun top s v => SG rt p m root pp mlo mhi z w0 w1 w2 V s v ∧ top < s.next ∧ v top = kw (tw2 idx 0))
    (fun s a s' v _ hp he hq => ⟨hp.mono he, hq⟩) fun top => ?_
  refine CGood.seq (k₂ := 0) ((CGood.hyp fun (hl : ((w0 ++ w1 ++ w2).take 26).length = 26 ∧
      (∀ κ < 14, (((List.range 15).map fun k => ((w0 ++ w1 ++ w2).drop (26 + 10 * k)).take 10).getD κ []).length = 10) ∧
      pp.length = 2) => fts_cg ((w0 ++ w1 ++ w2).take 26)
      ((List.range 15).map fun k => ((w0 ++ w1 ++ w2).drop (26 + 10 * k)).take 10) top pp idx u p (secN sig)
      (ftsPathN sig) hl.1 hidx hl.2.1 hu hl.2.2).pre fun s v h => ⟨⟨by simp only [List.length_take, hlen s v h.1]; norm_num,
        fun κ hκ => by rw [us_getD' _ κ (by omega)]; simp only [List.length_take, List.length_drop, hlen s v h.1]; omega,
        h.1.1.2.1.1⟩,
        hidxBL s v h.1, fun κ hκ => huBL s v h.1 κ (by omega), h.2.1, h.2.2, h.1.1.2.1.ppw⟩)
    (P₂ := fun msg s v => SG rt p m root pp mlo mhi z w0 w1 w2 V s v ∧ msg < s.next ∧ ∃ Dn : Fin 4 → W, v msg = dVal Dn ∧ (Dn 0, Dn 1) = key)
    (fun s a s' v _ hp he hq => ⟨hp.1.mono he, hq.1, Kd, hq.2, hKd⟩) fun msg0 => ?_
  have hGb : ∀ s v, SG rt p m root pp mlo mhi z w0 w1 w2 V s v → BL ((w0 ++ w1 ++ w2).take 26) idx s v ∧ PPw pp p s v :=
    fun s v h => ⟨hidxBL s v h, h.1.2.1.ppw⟩
  refine (CGood.seq (k₂ := 0) ((forIn_cgood 0 _ [2, 1, 0]
      (fun i nd s v => (SG rt p m root pp mlo mhi z w0 w1 w2 V s v ∧ LayBus j i s v) ∧ nd < s.next ∧
        ∃ Dn : Fin 4 → W, v nd = dVal Dn ∧ (Dn 0, Dn 1) = [key, r1, r2, rt].getD i (0, 0)) ?_ msg0).pre
      fun s v h => ⟨⟨h.1, fun lay hl h3 => absurd h3 (by omega)⟩, h.2⟩)
    (P₂ := fun r s v => (SG rt p m root pp mlo mhi z w0 w1 w2 V s v ∧ ∀ lay < 3, SigBus (3 * j + lay) 103 s v) ∧
      r < s.next ∧ ∃ Dn : Fin 4 → W, v r = dVal Dn ∧ (Dn 0, Dn 1) = rt)
    (fun s r s' v _ _ _ hq => ⟨⟨hq.1.1, fun lay hl => hq.1.2 lay hl
      (by simp only [List.length_cons, List.length_nil]; omega)⟩, hq.2⟩) fun r => ?_).kEq
    (by simp)
  · intro i hi b
    simp only [List.length_cons, List.length_nil] at hi
    try dsimp only
    have hcl := fun (lay : ℕ) (hlay : lay < 3) (hli : lay + i = 2) (Rin Rout : Dig)
        (hlr : Words.layerRoot p idx sig Rin ⟨lay, hlay⟩ = some Rout) =>
      ((CGood.hyp (st := st) fun (hl : ((w0 ++ w1 ++ w2).take 26).length = 26 ∧ pp.length = 2) =>
        layer_step j lay hlay (by omega) ((w0 ++ w1 ++ w2).take 26) pp b idx p sig Rin Rout
          (fun s v => SG rt p m root pp mlo mhi z w0 w1 w2 V s v ∧ LayBus j i s v)
          (fun _ _ _ h he => ⟨h.1.mono he, h.2.mono he⟩) (fun s v h => hGb s v h.1) hl.1 hidx hl.2 hlr).pre
        (P' := fun s v => (SG rt p m root pp mlo mhi z w0 w1 w2 V s v ∧ LayBus j i s v) ∧ b < s.next ∧
          ∃ Dn : Fin 4 → W, v b = dVal Dn ∧ (Dn 0, Dn 1) = Rin)
        fun s v h => ⟨⟨by simp only [List.length_take, hlen s v h.1.1]; norm_num, h.1.1.1.2.1.1⟩, h⟩).weaken
        (Q' := fun _ r s' v => ∃ b', r = ForInStep.yield b' ∧ (SG rt p m root pp mlo mhi z w0 w1 w2 V s' v ∧
          LayBus j (i + 1) s' v) ∧ b' < s'.next ∧ ∃ Dn : Fin 4 → W, v b' = dVal Dn ∧ (Dn 0, Dn 1) = Rout)
        (fun _ _ h => h) fun _ _ _ _ _ _ _ h => by
          obtain ⟨b', hb', ⟨⟨hsg, hbus⟩, hnew⟩, hlt, hD⟩ := h
          refine ⟨b', hb', ⟨hsg, fun lay' hl' h3 => ?_⟩, hlt, hD⟩
          by_cases hx : lay' = lay
          · rw [hx]; exact hnew
          · exact hbus lay' hl' (by omega)
    interval_cases i
    · exact hcl 2 (by norm_num) (by norm_num) key r1 hl2
    · exact hcl 1 (by norm_num) (by norm_num) r1 r2 hl1
    · exact hcl 0 (by norm_num) (by norm_num) r2 rt hl0
  try dsimp only
  refine CGood.seq (k₂ := 0) ((dToK_cgood r).pre fun s v h => h.2.1)
    (P₂ := fun rs s v => (SH4 rt p m root pp mlo mhi s v ∧ ∀ lay < 3, SigBus (3 * j + lay) 103 s v) ∧
      rs.length = 4 ∧ Wires rs s ∧ v (rs.getD 0 0) = kw rt.1 ∧ v (rs.getD 1 0) = kw rt.2)
    (fun s rs s' v _ hp he hq => by
      obtain ⟨⟨hg, hbus⟩, -, Dn, hDn, hrt⟩ := hp
      refine ⟨⟨hg.1.mono he, fun lay hl => (hbus lay hl).mono he⟩, hq.1, hq.2.1, (hq.2.2 0).trans ?_,
        (hq.2.2 1).trans ?_⟩
      · rw [hDn, ← hrt]; rfl
      · rw [hDn, ← hrt]; rfl) fun rs => ?_
  have hroot : ∀ s v, SH4 rt p m root pp mlo mhi s v → ∀ i < 2, root.getD i 0 < s.next ∧ v (root.getD i 0) = kw ([rt.1, rt.2].getD i 0) :=
    fun s v h i hi => ⟨h.1.2.1 _ (getD_mem (by rw [h.1.1]; simpa using hi)), h.1.2.2 i (by rw [h.1.1]; simpa using hi)⟩
  refine CGood.seq (k₂ := 0) ((union_cgood _ _).pre fun s v h => ⟨h.2.2.1 _ (getD_mem (by rw [h.2.1]; norm_num)),
      (hroot s v h.1.1 0 (by norm_num)).1, by rw [h.2.2.2.1, (hroot s v h.1.1 0 (by norm_num)).2]; rfl⟩)
    (P₂ := fun _ s v => (SH4 rt p m root pp mlo mhi s v ∧ ∀ lay < 3, SigBus (3 * j + lay) 103 s v) ∧
      rs.length = 4 ∧ Wires rs s ∧ v (rs.getD 0 0) = kw rt.1 ∧ v (rs.getD 1 0) = kw rt.2)
    (fun s _ s' v _ hp he _ => ⟨⟨hp.1.1.mono he, fun lay hl => (hp.1.2 lay hl).mono he⟩, hp.2.1,
      hp.2.2.1.mono he, hp.2.2.2⟩) fun _ => ?_
  exact ((union_cgood _ _).pre fun s v h => ⟨h.2.2.1 _ (getD_mem (by rw [h.2.1]; norm_num)),
      (hroot s v h.1.1 1 (by norm_num)).1, by rw [h.2.2.2.2, (hroot s v h.1.1 1 (by norm_num)).2]; rfl⟩).weaken
    (fun _ _ h => h) fun _ _ _ _ _ hP he _ => fun lay hl => (hP.1.2 lay hl).mono he

end

/-! The circuit. -/

section

variable {st : ℕ → Fin 4 → K}

/-- The circuit of `n ≤ 2^20` signatures: each layer's tag's rows on the bus balance. -/
theorem circuit_cg (n : ℕ) (hn : n ≤ 2 ^ 20) (h : ∀ j < n, ∃ root pp msg, Encodes st j root pp msg ∧
      ∃ sig, Words.verify root pp msg sig = true) :
    CGood st (4 * n) (fun s _ => s.statement = 0) (Circuit.circuit n) fun _ _ s' v =>
      ∀ g < 3 * n, SigBus g 103 s' v := by
  unfold Circuit.circuit
  refine (CGood.seq (k₂ := 0) ((forIn_cgood 4 _ (List.range n)
      (fun i _ s v => s.statement = 4 * i ∧ ∀ g < 3 * i, SigBus g 103 s v) ?_ PUnit.unit).pre
      fun s _ h => ⟨by rw [h], fun g hg => absurd hg (by omega)⟩)
    (P₂ := fun _ s v => ∀ g < 3 * n, SigBus g 103 s v)
    (fun s _ s' v _ _ _ hq => by simp only [List.length_range] at hq; exact hq.2) fun _ =>
      CGood.pure' fun _ _ _ h => h).kEq (by simp)
  intro i hi b
  simp only [List.length_range] at hi
  try simp only [List.getElem_range]
  obtain ⟨root, pp, msg, henc, sig, hv⟩ := h i hi
  refine CGood.seq (k₂ := 0) ((signature_cg i (by omega) root pp msg sig henc hv).stmt.pre fun s v h => h.1)
    (P₂ := fun _ s v => s.statement = 4 * (i + 1) ∧ ∀ g < 3 * (i + 1), SigBus g 103 s v)
    (fun s _ s' v _ hp he hq => ⟨by rw [hq.2, hp.1]; ring, fun g hg => ?_⟩)
    fun _ => CGood.pure' fun _ _ _ h => ⟨_, rfl, h⟩
  by_cases hgi : g < 3 * i
  · exact (hp.2 g hgi).mono he
  · have := hq.1 (g - 3 * i) (by omega)
    rwa [show 3 * i + (g - 3 * i) = g by omega] at this

end

/-- The honest assignment of the circuit verifying `n ≤ 2^20` leanSPHINCS signatures: it satisfies the rows, and its
bus balances because each layer's rows do, and the rows the layers name are all the circuit's
(`Sphincs.count_circuit`, `rows_perm`). -/
theorem circuit_complete (n : ℕ) (hn : n ≤ 2 ^ 20) (st : ℕ → Fin 4 → K)
    (h : ∀ j < n, ∃ root pp msg, Encodes st j root pp msg ∧ ∃ sig, Words.verify root pp msg sig = true) :
    ∃ val, Accepts st ((Circuit.circuit n).run {}).2 val := by
  obtain ⟨-, -, -, -, val', -, hsat, hq⟩ :=
    circuit_cg n hn h {} (fun _ _ => 0) inv_empty closed_empty (sat_empty st _) fun _ _ => rfl
  have hbus := hq val' (Agree.refl _ _)
  have hex : ∀ g, ∃ R L : List (List ℕ), g < 3 * n →
      BusRows g 103 ((Circuit.circuit n).run {}).2 val' R L := fun g => by
    by_cases hg : g < 3 * n
    · obtain ⟨R, L, hb⟩ := hbus g hg
      exact ⟨R, L, fun _ => hb⟩
    · exact ⟨[], [], fun h => absurd h hg⟩
  choose Rs Ls hRL using hex
  have hsize := Sphincs.count_circuit n {}
  simp only [Array.size_empty, Nat.zero_add] at hsize
  have hRnd := nodup_flatMap_label (3 * n) Rs (fun r => toWord (val' (r.getD 4 0) 0) / 2 ^ 41)
    (fun g hg => (hRL g hg).2.2.1) fun g hg => (hRL g hg).2.2.2.2.2.2.1
  have hLnd := nodup_flatMap_label (3 * n) Ls (fun r => toWord (val' (r.getD 0 0) 0) / 2 ^ 41 % 2 ^ 22)
    (fun g hg => (hRL g hg).2.2.2.1) fun g hg => (hRL g hg).2.2.2.2.2.2.2.1
  have hR := rows_perm _ (3 * n) 103 Rs (by rw [hsize.1]; ring) (fun g hg => (hRL g hg).1)
    (fun g hg => (hRL g hg).2.2.2.2.1) hRnd
  have hL := rows_perm _ (3 * n) 42 Ls (by rw [hsize.2]; ring) (fun g hg => (hRL g hg).2.1)
    (fun g hg => (hRL g hg).2.2.2.2.2.1) hLnd
  exact ⟨val', hsat, balanced_of_local _ val' (3 * n) Rs Ls hR hL fun g hg => (hRL g hg).2.2.2.2.2.2.2.2⟩

end LeanVMCircuits.Sphincs.Complete

namespace LeanVMCircuits.Sphincs

open LeanVMCircuits.Rec LeanVMCircuits.Rec.Model

/-- Completeness: when every signature's statement words encode a root, public parameter and message with a
signature `Words.verify` accepts, the machine accepts the circuit verifying `n ≤ 2^20` leanSPHINCS signatures with
some assignment (`Accepts`: its rows satisfied and its dynamic bus balanced). -/
theorem complete (n : ℕ) (hn : n ≤ 2 ^ 20) (st : ℕ → Fin 4 → K)
    (h : ∀ j < n, ∃ root pp msg, Encodes st j root pp msg ∧ ∃ sig, Words.verify root pp msg sig = true) :
    ∃ val, Accepts st ((Circuit.circuit n).run {}).2 val :=
  Complete.circuit_complete n hn st h

end LeanVMCircuits.Sphincs
