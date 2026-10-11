module

public import LeanVMCircuits.Xmss.CompleteBuilder
public import LeanVMCircuits.Xmss.Statement
public import LeanVMCircuits.Xmss.FieldFacts

@[expose] public section

/-!
# Completeness of the leanXMSS verifier circuit

Every signature `Words.verify` accepts, under statement words that encode it (`Encodes`), extends to an assignment
satisfying the circuit `Circuit.circuit n`. Each gadget of `Xmss.Circuit` gets a `CGood` contract built from the
builder's (`Xmss.CompleteBuilder`): the statement words carry the encoded words, the index word is the epoch's tweak
word, a tweak hash is BLAKE2s-256 of its words, the digit product is `x` to the digits' sum, the indicators are those
of the digit, a chain ends at `Words.chainFrom`, a level is `Words.parent`. The signature's contract runs them in
order from the encoding the verification found: the high bits and the sum of the digits hold because `encode`
succeeded, and the root exposed is the statement's because the path climbs to it.
-/

namespace LeanVMCircuits.Xmss

open LeanVMCircuits.Rec LeanVMCircuits.Rec.Model

/-! Words on wires. -/

/-- A `K` wire's limbs carrying the word `x`. -/
noncomputable def kw (x : Words.W) : Fin 4 → K := kVal (ofWord x.toNat)

theorem w64_kw {v : Val} {w : ℕ} {x : Words.W} (h : v w = kw x) : w64 v w = x := by
  have h0 : v w 0 = ofWord x.toNat := by rw [h]; rfl
  rw [w64, h0, toWord_ofWord _ x.isLt]
  simp

theorem kw_zero : kw 0 = kVal 0 := by simp [kw, ofWord_zero]

theorem kw_isK {v : Val} {w : ℕ} {x : Words.W} (h : v w = kw x) : v w = kVal (v w 0) := by
  rw [h]; rfl

theorem limbs3_three (a b c : Words.W) : limbs3 a b c 3 = 0 := rfl

section

variable {st : ℕ → Fin 4 → K}

/-- `words`: an `E` wire's first three limbs as `K` words. -/
theorem words_cg (e : ℕ) : CGood st 0 (fun s v => e < s.next ∧ v e 3 = 0) (Circuit.words e)
    fun _ r s' v => (r.1 < s'.next ∧ r.2.1 < s'.next ∧ r.2.2 < s'.next) ∧ v r.1 = kVal (v e 0) ∧
      v r.2.1 = kVal (v e 1) ∧ v r.2.2 = kVal (v e 2) := by
  unfold Circuit.words
  refine (CGood.bind (eToK_cgood e) (P₂ := fun _ _ _ => True) (fun _ _ _ _ _ _ _ _ => trivial) fun ks =>
    CGood.pure' (Q := fun _ r _ _ => r = (ks.getD 0 0, ks.getD 1 0, ks.getD 2 0)) fun _ _ _ _ => rfl).weaken
    (fun _ _ h => h) ?_
  rintro s r s' v hs - - ⟨ks, s1, -, he, -, ⟨hlen, hw, hv⟩, rfl⟩
  have hw' := hw.mono he
  exact ⟨⟨hw' _ (getD_mem (by omega)), hw' _ (getD_mem (by omega)), hw' _ (getD_mem (by omega))⟩,
    hv 0 (by decide), hv 1 (by decide), hv 2 (by decide)⟩

/-- `statementWords`: the statement word `[a, b, c]` exposed, its first `3 - zeros` words, the rest zero. -/
theorem statementWords_cg (zeros : ℕ) (a b c : Words.W)
    (hz : (zeros = 1 ∧ c = 0) ∨ (zeros = 2 ∧ b = 0 ∧ c = 0)) :
    CGood st 1 (fun s _ => st s.statement = limbs3 a b c) (Circuit.statementWords zeros)
      fun _ ws s' v => ws.length = 3 - zeros ∧ Wires ws s' ∧
        ∀ i < 3 - zeros, v (ws.getD i 0) = kw ([a, b, c].getD i 0) := by
  apply CGood.intro
  intro s₀ val₀
  unfold Circuit.statementWords
  have hks : ∀ (ks : List ℕ) (s : State) (v : Val), ks.length = 3 → Wires ks s →
      (∀ i : Fin 4, i.val < 3 → v (ks.getD i 0) = kVal (limbs3 a b c i)) →
      ∀ i < 3, v (ks.getD i 0) = kw ([a, b, c].getD i 0) := by
    intro ks s v _ _ hv i hi
    interval_cases i
    · exact (hv 0 (by decide)).trans rfl
    · exact (hv 1 (by decide)).trans rfl
    · exact (hv 2 (by decide)).trans rfl
  refine ((CGood.bind ((wire_cgood (limbs3 a b c)).stmt.pre
      (P' := fun s v => s = s₀ ∧ Agree s.next val₀ v ∧ st s.statement = limbs3 a b c) fun _ _ _ => trivial)
    (P₂ := fun w s v => w < s.next ∧ v w = st s.statement ∧ st s.statement = limbs3 a b c)
    (fun s w s' v _ hp _ hq => ⟨by rw [hq.1.2.1, hq.1.1]; exact Nat.lt_succ_self _,
      by rw [hq.1.2.2, hq.2, Nat.add_zero, hp.2.2], by rw [hq.2, Nat.add_zero, hp.2.2]⟩) fun w =>
    CGood.bind ((expose_cgood w).pre fun _ _ h => ⟨h.1, h.2.1⟩) (P₂ := fun _ s v => w < s.next ∧ v w = limbs3 a b c)
      (fun s _ s' v _ hp he _ => ⟨lt_of_lt_of_le hp.1 he.next, hp.2.1.trans hp.2.2⟩) fun _ =>
    CGood.bind ((eToK_cgood w).pre fun _ _ h => ⟨h.1, by rw [h.2]; rfl⟩)
      (P₂ := fun ks s v => ks.length = 3 ∧ Wires ks s ∧ ∀ i < 3, v (ks.getD i 0) = kw ([a, b, c].getD i 0))
      (fun s ks s' v _ hp he hq => ⟨hq.1, hq.2.1, hks ks s' v hq.1 hq.2.1 fun i hi => by
        rw [hq.2.2 i hi, hp.2]⟩) fun ks =>
    CGood.bind (forIn_unit_cgood (ks.drop (3 - zeros)) (fun k => eqConstK k 0)
        (fun s v => ks.length = 3 ∧ Wires ks s ∧ ∀ i < 3, v (ks.getD i 0) = kw ([a, b, c].getD i 0))
        (fun _ _ _ h he => ⟨h.1, h.2.1.mono he, h.2.2⟩) fun i hi => (eqConstK_cgood _ 0).pre ?_)
      (P₂ := fun _ s v => ks.length = 3 ∧ Wires ks s ∧ ∀ i < 3, v (ks.getD i 0) = kw ([a, b, c].getD i 0))
      (fun _ _ _ _ _ hp he _ => ⟨hp.1, hp.2.1.mono he, hp.2.2⟩) fun _ =>
    CGood.pure' (Q := fun _ r _ _ => r = ks.take (3 - zeros)) fun _ _ _ _ => rfl).weaken (fun _ _ h => h) ?_).kEq
    (by rfl)
  · rintro s v ⟨hlen, hw, hv⟩
    have hzr : zeros ≤ 2 := by omega
    have hi' : i < zeros := by simp [hlen] at hi; omega
    have hi3 : 3 - zeros + i < 3 := by omega
    have hget : (ks.drop (3 - zeros))[i] = ks.getD (3 - zeros + i) 0 := by
      rw [List.getElem_drop, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [hget]
    refine ⟨hw _ (getD_mem (by omega)), ?_⟩
    rw [hv _ hi3]
    have : [a, b, c].getD (3 - zeros + i) 0 = 0 := by
      rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · have : i = 0 := by omega
        subst this; rfl
      · interval_cases i <;> rfl
    rw [this, kw_zero, ofWord_zero]
  · rintro s r s5 v hs - - ⟨w, s1, -, -, -, -, i, s2, -, -, -, -, ks, s3, -, he35, -, -, u, s4, -, -,
      ⟨hlen, hw, hv⟩, -, rfl⟩
    have hm : 3 - zeros ≤ 3 := by omega
    refine ⟨by simp [hlen], fun u hu => (hw.mono he35) u (List.mem_of_mem_take hu), fun i hi => ?_⟩
    have : (ks.take (3 - zeros)).getD i 0 = ks.getD i 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_take, hi]
    rw [this]
    exact hv i (by omega)

end

/-- The word an index's bits pack to: `e >> shift` in the high half. -/
theorem index_num (e shift : ℕ) (he : e < 2 ^ 32) (c : ℕ → ZMod 2)
    (hc : ∀ i < 64, c i = if 32 ≤ i ∧ e.testBit (i - 32 + shift) = true then 1 else 0) :
    num c 64 = e / 2 ^ shift * 2 ^ 32 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · rw [testBit_num c 64 i hi, hc i hi, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow]
    by_cases h32 : 32 ≤ i
    · by_cases ht : e.testBit (i - 32 + shift) = true <;> simp [h32, ht]
    · simp [h32]
  · have h1 : e / 2 ^ shift * 2 ^ 32 < 2 ^ i := by
      calc e / 2 ^ shift * 2 ^ 32 ≤ e * 2 ^ 32 := Nat.mul_le_mul_right _ (Nat.div_le_self _ _)
        _ < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right he (by positivity)
        _ = 2 ^ 64 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (num_lt c 64) (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow h1]

section

variable {st : ℕ → Fin 4 → K}

/-- Wires `bits` carrying the bits of `e`. -/
def BitsOf (bits : List ℕ) (e : ℕ) (s : State) (v : Val) : Prop :=
  bits.length = 64 ∧ Wires bits s ∧ ∀ i < 64, v (bits.getD i 0) = kVal (bitK e i)

theorem BitsOf.mono {bits : List ℕ} {e : ℕ} {s s' : State} {v : Val} (h : BitsOf bits e s v) (he : Ext s s') :
    BitsOf bits e s' v :=
  ⟨h.1, h.2.1.mono he, h.2.2⟩

/-- `indexWord`: the tweak word of `e >> shift`. -/
theorem indexWord_cg (bits : List ℕ) (shift e : ℕ) (he : e < 2 ^ 32) (hs : shift ≤ 32) :
    CGood st 0 (fun s v => BitsOf bits e s v) (Circuit.indexWord bits shift)
      fun _ r s' v => r < s'.next ∧ v r = kw (Words.tweak1 (e / 2 ^ shift)) := by
  unfold Circuit.indexWord
  set l : ℕ → List ℕ := fun z => List.replicate 32 z ++ List.drop shift (List.take 32 bits)
  have hll : ∀ z, bits.length = 64 → (l z).length = 64 - shift := by
    intro z hb; simp [l, hb]; omega
  have hl : ∀ z i, bits.length = 64 → i < 64 - shift →
      (l z).getD i 0 = if i < 32 then z else bits.getD (i - 32 + shift) 0 := by
    intro z i hb hi
    simp only [l, List.getD_eq_getElem?_getD]
    split_ifs with h1
    · rw [List.getElem?_append_left (by simpa using h1), List.getElem?_replicate, if_pos h1]
      rfl
    · rw [List.getElem?_append_right (by simp; omega), List.getElem?_drop, List.getElem?_take]
      simp only [List.length_replicate]
      rw [if_pos (by omega), show shift + (i - 32) = i - 32 + shift by omega]
  refine (CGood.bind ((kConst_cgood 0).pre (P' := fun s v => BitsOf bits e s v) fun _ _ _ => trivial)
    (P₂ := fun z s v => BitsOf bits e s v ∧ z < s.next ∧ v z = kVal 0)
    (fun _ _ _ _ _ hp he hq => ⟨hp.mono he, hq.1, by rw [hq.2, ofWord_zero]⟩)
    fun z => (pack_cgood (l z)).pre fun s v h => ?_).weaken (fun _ _ h => h) ?_
  · obtain ⟨⟨hb, hw, hv⟩, hz, hzv⟩ := h
    refine ⟨fun u hu => ?_, by rw [hll z hb]; omega, fun i hi => ?_⟩
    · rcases List.mem_append.mp hu with hu | hu
      · rw [List.eq_of_mem_replicate hu]; exact hz
      · exact hw u (List.mem_of_mem_take (List.mem_of_mem_drop hu))
    · rw [hll z hb] at hi
      rw [hl z i hb hi]
      split_ifs with h1
      · exact Or.inl hzv
      · rw [hv _ (by omega)]
        by_cases ht : e.testBit (i - 32 + shift) = true
        · exact Or.inr ((kVal_bitK_eq_one _ _).mpr ht)
        · left; simp [bitK, ht]
  · rintro s r s2 v hs hb - ⟨z, s1, -, -, -, ⟨hz, hzv⟩, hr, hrv⟩
    obtain ⟨hbl, hbw, hbv⟩ := hb
    refine ⟨hr, ?_⟩
    have hlt : e / 2 ^ shift < 2 ^ 32 := lt_of_le_of_lt (Nat.div_le_self _ _) he
    have h64 : e / 2 ^ shift * 2 ^ 32 < 2 ^ 64 := by
      calc e / 2 ^ shift * 2 ^ 32 < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hlt (by positivity)
        _ = 2 ^ 64 := by norm_num
    have hk01 : kVal (0 : K) ≠ kVal 1 := fun h => zero_ne_one (kVal_inj h)
    have hnum : num (fun i => if i < (l z).length ∧ v ((l z).getD i 0) = kVal 1 then 1 else 0) 64 =
        (Words.tweak1 (e / 2 ^ shift)).toNat := by
      rw [index_num e shift he _ ?_, Words.tweak1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt h64]
      intro i hi
      by_cases hil : i < 64 - shift
      · simp only [hll z hbl, hl z i hbl hil]
        by_cases h32 : i < 32
        · rw [if_pos h32, hzv, ofWord_zero, if_neg (fun h => hk01 h.2), if_neg (by omega)]
        · rw [if_neg h32, hbv _ (by omega)]
          by_cases ht : e.testBit (i - 32 + shift) = true
          · rw [if_pos ⟨hil, (kVal_bitK_eq_one _ _).mpr ht⟩, if_pos ⟨by omega, ht⟩]
          · rw [if_neg (fun h => ht ((kVal_bitK_eq_one _ _).mp h.2)), if_neg (fun h => ht h.2)]
      · simp only [hll z hbl]
        rw [if_neg (fun h => hil h.1), if_neg]
        rintro ⟨-, ht⟩
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le he (Nat.pow_le_pow_right (by norm_num) (by omega)))] at ht
        exact Bool.false_ne_true ht
    rw [hrv]
    exact congrArg (fun n => kVal (ofWord n)) hnum

/-- `tweakHash`: the hash of the tweak, the index word, the parameter and the payload. -/
theorem tweakHash_cg (ty pos idx : ℕ) (pp payload : List ℕ) (htw : Circuit.tweak0 ty pos < 2 ^ 64)
    (hlen : pp.length + payload.length ≤ 100) :
    CGood st 0 (fun s v => Wires (idx :: pp ++ payload) s ∧ ∀ w ∈ idx :: pp ++ payload, v w = kVal (v w 0))
      (Circuit.tweakHash ty pos idx pp payload) fun _ d s' v => d < s'.next ∧
        v d = dVal (digest (hashWords (Words.tweak0 ty pos :: (idx :: pp ++ payload).map (w64 v)))) := by
  have hb : ∀ tw : ℕ, 8 * ([tw, idx] ++ pp ++ payload).length < 2 ^ 64 := fun tw => by
    simp only [List.length_append, List.length_cons, List.length_nil]
    have : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
    omega
  have hk : ∀ (tw : ℕ) (v : Val), (∀ w ∈ idx :: pp ++ payload, v w = kVal (v w 0)) →
      v tw = kVal (ofWord (Circuit.tweak0 ty pos)) → ∀ w ∈ tw :: idx :: pp ++ payload, v w = kVal (v w 0) := by
    intro tw v hp htw w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact kVal_isK htw
    · exact hp w hw
  unfold Circuit.tweakHash
  refine (CGood.bind ((kConst_cgood _).pre (P' := fun s v => Wires (idx :: pp ++ payload) s ∧
      ∀ w ∈ idx :: pp ++ payload, v w = kVal (v w 0)) fun _ _ _ => trivial)
    (P₂ := fun tw s v => Wires (tw :: idx :: pp ++ payload) s ∧
      (∀ w ∈ tw :: idx :: pp ++ payload, v w = kVal (v w 0)) ∧ v tw = kVal (ofWord (Circuit.tweak0 ty pos)))
    (fun _ tw _ v _ hp he hq => ⟨wires_cons.2 ⟨hq.1, hp.1.mono he⟩, hk tw v hp.2 hq.2, hq.2⟩)
    fun tw => (chain_cgood ([tw, idx] ++ pp ++ payload) (hb tw)).pre fun _ _ h => ⟨h.1, h.2.1⟩).weaken (fun _ _ h => h) ?_
  rintro s d s2 v hs - - ⟨tw, s1, -, -, -, ⟨htwl, htwv⟩, hd, hdv⟩
  refine ⟨hd, ?_⟩
  have hw : w64 v tw = Words.tweak0 ty pos := by
    rw [w64, htwv, kVal_apply_zero, toWord_ofWord _ htw, Words.tweak0]
  have hl : ([tw, idx] ++ pp ++ payload).map (w64 v) =
      Words.tweak0 ty pos :: (idx :: pp ++ payload).map (w64 v) := by
    simp only [List.cons_append, List.nil_append, List.map_cons, hw]
  rw [hdv, hl]

end

/-! The digit product and the indicators. -/

/-- The low `k` bits' weights of digit `i`, from its bits `B (3 i + k')`. -/
def dig (B : ℕ → Bool) (i k : ℕ) : ℕ := ((List.range k).map fun k' => if B (3 * i + k') then 2 ^ k' else 0).sum

/-- The first `i` digits' sum. -/
def psum (B : ℕ → Bool) (i : ℕ) : ℕ := ((List.range i).map fun i' => dig B i' 3).sum

theorem dig_succ (B : ℕ → Bool) (i k : ℕ) : dig B i (k + 1) = dig B i k + if B (3 * i + k) then 2 ^ k else 0 := by
  simp [dig, List.range_succ]

theorem psum_succ (B : ℕ → Bool) (i : ℕ) : psum B (i + 1) = psum B i + dig B i 3 := by
  simp [psum, List.range_succ]

theorem getElem_eq_getD (l : List ℕ) (i : ℕ) (h : i < l.length) : l[i] = l.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem emb_ite (c : Prop) [Decidable c] : emb (if c then 1 else 0) = if c then 1 else 0 := by
  split_ifs <;> simp [emb]

section

variable {st : ℕ → Fin 4 → K}

/-- The digit product's context: the bits' wires and the zero. -/
def DPCtx (bits : List ℕ) (B : ℕ → Bool) (z : ℕ) (s : State) (v : Val) : Prop :=
  bits.length = 126 ∧ Wires bits s ∧ (∀ j < 126, v (bits.getD j 0) = kVal (if B j then 1 else 0)) ∧
    z < s.next ∧ v z = eVal 0

theorem DPCtx.mono {bits : List ℕ} {B : ℕ → Bool} {z : ℕ} {s s' : State} {v : Val} (h : DPCtx bits B z s v)
    (he : Ext s s') : DPCtx bits B z s' v :=
  ⟨h.1, h.2.1.mono he, h.2.2.1, lt_of_lt_of_le h.2.2.2.1 he.next, h.2.2.2.2⟩

theorem dp_step (bits : List ℕ) (B : ℕ → Bool) (z i k acc a : ℕ) (hi : i < 42) (hk : k < 3) :
    CGood st 0 (fun s v => DPCtx bits B z s v ∧ acc < s.next ∧ v acc = eVal (emb (root ^ a)))
      (do
        let t ← mulConstAdd acc (2 ^ 2 ^ k + 1) 0 0 z
        let acc ← mulKAdd t (bits.getD (3 * i + k) 0) acc
        pure (ForInStep.yield acc))
      fun _ r s' v => ∃ b', r = .yield b' ∧ DPCtx bits B z s' v ∧ b' < s'.next ∧
        v b' = eVal (emb (root ^ (a + if B (3 * i + k) then 2 ^ k else 0))) := by
  refine (CGood.bind ((mulConstAdd_cgood acc (2 ^ 2 ^ k + 1) 0 0 z).pre fun s v h =>
      ⟨wires2 h.2.1 h.1.2.2.2.1, by rw [h.2.2]; rfl, by rw [h.1.2.2.2.2]; rfl⟩)
    (P₂ := fun t s v => DPCtx bits B z s v ∧ acc < s.next ∧ v acc = eVal (emb (root ^ a)) ∧ t < s.next ∧
      v t = eVal (emb (root ^ a * (root ^ 2 ^ k + 1))))
    (fun s t s' v _ hp he hq => ⟨hp.1.mono he, lt_of_lt_of_le hp.2.1 he.next, hp.2.2, hq.1, by
      rw [hq.2, ev_of_eVal hp.2.2, ev_of_eVal hp.1.2.2.2.2, ofWord_zero, toE_emb, ofWord_weight k hk, add_zero,
        emb_mul]⟩) fun t =>
    CGood.bind ((mulKAdd_cgood t (bits.getD (3 * i + k) 0) acc).pre fun s v h => ⟨wires3 h.2.2.2.1
      (h.1.2.1 _ (getD_mem (by rw [h.1.1]; omega))) h.2.1, by rw [h.2.2.2.2]; rfl,
      by rw [h.1.2.2.1 _ (by omega)]; rfl, by rw [h.2.2.1]; rfl⟩)
      (P₂ := fun _ _ _ => True) (fun _ _ _ _ _ _ _ _ => trivial) fun acc' =>
      CGood.pure' (Q := fun _ r _ _ => r = .yield acc') fun _ _ _ _ => rfl).weaken (fun _ _ h => h) ?_
  rintro s r s3 v hs hp - ⟨t, s1, -, he13, -, -, acc', s2, -, he23, ⟨hc, -, hacc, -, htv⟩, ⟨hr, hrv⟩, rfl⟩
  refine ⟨acc', rfl, hc.mono he13, lt_of_lt_of_le hr he23.next, ?_⟩
  rw [hrv, ev_of_eVal htv, ev_of_eVal hacc, hc.2.2.1 _ (by omega)]
  congr 1
  cases B (3 * i + k)
  · simp [kVal, emb_zero]
  · simp only [kVal, if_true, Matrix.cons_val_zero, pow_add, ← emb_mul, ← emb_add]
    congr 1
    linear_combination root ^ a * two_K

/-- `digitProduct`: `x` to the power of the digits' sum. -/
theorem digitProduct_cg (bits : List ℕ) (B : ℕ → Bool) :
    CGood st 0 (fun s v => bits.length = 126 ∧ Wires bits s ∧
      ∀ j < 126, v (bits.getD j 0) = kVal (if B j then 1 else 0)) (Circuit.digitProduct bits)
      fun _ r s' v => r < s'.next ∧ v r = eVal (emb (root ^ psum B 42)) := by
  unfold Circuit.digitProduct
  refine (CGood.bind (one_cgood.pre fun _ _ _ => trivial)
    (P₂ := fun o s v => (bits.length = 126 ∧ Wires bits s ∧
      ∀ j < 126, v (bits.getD j 0) = kVal (if B j then 1 else 0)) ∧ o < s.next ∧ v o = eVal 1)
    (fun _ _ _ _ _ hp he hq => ⟨⟨hp.1, hp.2.1.mono he, hp.2.2⟩, hq⟩) fun acc =>
    CGood.bind (zero_cgood.pre fun _ _ _ => trivial)
      (P₂ := fun z s v => DPCtx bits B z s v ∧ acc < s.next ∧ v acc = eVal (emb (root ^ psum B 0)))
      (fun _ _ _ _ _ hp he hq => ⟨⟨hp.1.1, hp.1.2.1.mono he, hp.1.2.2, hq.1, hq.2⟩,
        lt_of_lt_of_le hp.2.1 he.next, by rw [hp.2.2]; simp [psum, emb]⟩) fun z =>
      CGood.bind (forIn_cgood 0 _ (List.range 42)
        (fun i a s v => DPCtx bits B z s v ∧ a < s.next ∧ v a = eVal (emb (root ^ psum B i))) ?_ acc)
        (P₂ := fun _ _ _ => True) (fun _ _ _ _ _ _ _ _ => trivial) fun r =>
        CGood.pure' (Q := fun _ o _ _ => o = r) fun _ _ _ _ => rfl).weaken (fun _ _ h => h) ?_
  · intro i hi a
    simp only [List.length_range] at hi
    simp only [List.getElem_range]
    refine (CGood.bind (forIn_cgood 0 _ (List.range 3)
      (fun k a s v => DPCtx bits B z s v ∧ a < s.next ∧ v a = eVal (emb (root ^ (psum B i + dig B i k))))
      (fun k hk a => ?_) a |>.pre fun s v h => ⟨h.1, h.2.1, by rw [h.2.2]; simp [dig]⟩)
      (P₂ := fun _ _ _ => True) (fun _ _ _ _ _ _ _ _ => trivial) fun r =>
      CGood.pure' (Q := fun _ o _ _ => o = .yield r) fun _ _ _ _ => rfl).weaken (fun _ _ h => h) ?_
    · simp only [List.length_range] at hk
      simp only [List.getElem_range]
      refine (dp_step bits B z i k a (psum B i + dig B i k) hi hk).weaken (fun _ _ h => h) ?_
      rintro s r s' v - - - ⟨b', rfl, hc, hb, hbv⟩
      exact ⟨b', rfl, hc, hb, by rw [hbv, dig_succ, Nat.add_assoc]⟩
    · rintro s r s2 v hs - - ⟨r', s1, -, he, -, ⟨hc, hr, hrv⟩, rfl⟩
      exact ⟨r', rfl, hc.mono he, lt_of_lt_of_le hr he.next, by rw [hrv, psum_succ, List.length_range]⟩
  · rintro s r s4 v hs - - ⟨o, s1, -, -, -, -, z, s2, -, -, -, -, r', s3, -, he, -, ⟨-, hr, hrv⟩, rfl⟩
    exact ⟨lt_of_lt_of_le hr he.next, hrv⟩

/-- The digit of the bits `b 0, b 1, ...` below `m`. -/
def bdig (b : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | m + 1 => bdig b m + if b m then 2 ^ m else 0

theorem bdig_lt (b : ℕ → Bool) (m : ℕ) : bdig b m < 2 ^ m := by
  induction m with
  | zero => simp [bdig]
  | succ m ih => simp only [bdig, pow_succ]; split_ifs <;> omega

/-- Wires `l`, `n` of them, carrying the indicators of `d`. -/
def IndList (l : List ℕ) (n d : ℕ) (s : State) (v : Val) : Prop :=
  l.length = n ∧ Wires l s ∧ ∀ u < n, v (l.getD u 0) = eVal (if u = d then 1 else 0)

theorem IndList.mono {l : List ℕ} {n d : ℕ} {s s' : State} {v : Val} (h : IndList l n d s v) (he : Ext s s') :
    IndList l n d s' v :=
  ⟨h.1, h.2.1.mono he, h.2.2⟩

/-- The digit's bit wires. -/
def ABits (as : List ℕ) (b : ℕ → Bool) (s : State) (v : Val) : Prop :=
  as.length = 3 ∧ Wires as s ∧ ∀ m < 3, v (as.getD m 0) = kVal (if b m then 1 else 0)

theorem ABits.mono {as : List ℕ} {b : ℕ → Bool} {s s' : State} {v : Val} (h : ABits as b s v) (he : Ext s s') :
    ABits as b s' v :=
  ⟨h.1, h.2.1.mono he, h.2.2⟩

theorem ind_mul (p a z : ℕ) (v : Val) (c : Prop) [Decidable c] (β : Bool) (hp : v p = eVal (if c then 1 else 0))
    (ha : v a = kVal (if β then 1 else 0)) (hz : v z = eVal 0) :
    eVal (ev v p * emb (v a 0) + ev v p) = eVal (if c ∧ β = false then 1 else 0) ∧
      eVal (ev v p * emb (v a 0) + ev v z) = eVal (if c ∧ β = true then 1 else 0) := by
  rw [ev_of_eVal hp, ev_of_eVal hz, ha, kVal_apply_zero]
  have h2 : (1 : E) + 1 = 0 := by rw [one_add_one_eq_two, two_E]
  constructor <;> congr 1 <;> cases β <;> by_cases hc : c <;> simp [hc, emb, h2]

theorem ind_idx (u n d : ℕ) (β : Bool) (hd : d < n) (hu : u < 2 * n) :
    (u = d + if β then n else 0) ↔ (u % n = d ∧ (u < n ↔ β = false)) := by
  by_cases hun : u < n
  · rw [Nat.mod_eq_of_lt hun]; cases β <;> simp <;> omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; cases β <;> simp <;> omega

theorem ind_step (nx : List ℕ) (u d q : ℕ) (s : State) (v : Val) (c : Prop) [Decidable c]
    (hn : IndList nx u d s v) (hq : q < s.next) (hqv : v q = eVal (if c then 1 else 0)) (hc : c ↔ u = d) :
    IndList (nx ++ [q]) (u + 1) d s v := by
  obtain ⟨hl, hw, hv⟩ := hn
  refine ⟨by simp [hl], fun w hw' => ?_, fun u' hu' => ?_⟩
  · rcases List.mem_append.mp hw' with hw' | hw'
    · exact hw w hw'
    · rw [List.mem_singleton.mp hw']; exact hq
  · by_cases hlt : u' < u
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
      exact hv u' hlt
    · have : u' = u := by omega
      subst this
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl, Nat.sub_self]
      simp only [List.getElem?_cons_zero, Option.getD_some]
      rw [hqv]
      exact congrArg eVal (if_congr hc rfl rfl)

theorem indicators_cg (a0 a1 a2 : ℕ) (b : ℕ → Bool) :
    CGood st 0 (fun s v => ABits [a0, a1, a2] b s v) (Circuit.indicators a0 a1 a2)
      fun _ ind s' v => IndList ind 8 (bdig b 3) s' v := by
  unfold Circuit.indicators
  refine (CGood.bind (one_cgood.pre fun _ _ _ => trivial)
    (P₂ := fun o s v => ABits [a0, a1, a2] b s v ∧ o < s.next ∧ v o = eVal 1)
    (fun _ _ _ _ _ hp he hq => ⟨hp.mono he, hq⟩) fun o =>
    CGood.bind (zero_cgood.pre fun _ _ _ => trivial)
      (P₂ := fun z s v => (ABits [a0, a1, a2] b s v ∧ z < s.next ∧ v z = eVal 0) ∧ IndList [o] (2 ^ 0) (bdig b 0) s v)
      (fun _ _ _ _ _ hp he hq => ⟨⟨hp.1.mono he, hq⟩, rfl, wires_cons.2 ⟨lt_of_lt_of_le hp.2.1 he.next, wires_nil⟩,
        fun u hu => by
          have : u = 0 := by simpa using hu
          subst this
          rw [show ([o] : List ℕ).getD 0 0 = o from rfl, hp.2.2]
          simp [bdig]⟩) fun z =>
    CGood.bind (forIn_cgood 0 _ [a0, a1, a2]
        (fun m l s v => (ABits [a0, a1, a2] b s v ∧ z < s.next ∧ v z = eVal 0) ∧ IndList l (2 ^ m) (bdig b m) s v)
        ?_ [o])
      (P₂ := fun _ _ _ => True) (fun _ _ _ _ _ _ _ _ => trivial) fun r =>
      CGood.pure' (Q := fun _ x _ _ => x = r) fun _ _ _ _ => rfl).weaken (fun _ _ h => h) ?_
  · intro m hm l
    simp only [List.length_cons, List.length_nil] at hm
    dsimp only
    refine ((CGood.bind (forIn_cgood 0 _ (List.range (2 * l.length))
        (fun u nx s v => ((ABits [a0, a1, a2] b s v ∧ z < s.next ∧ v z = eVal 0) ∧
          IndList l (2 ^ m) (bdig b m) s v) ∧ IndList nx u (bdig b (m + 1)) s v) (fun u hu nx => ?_) []
        |>.pre fun s v h => ⟨h, rfl, wires_nil, fun u hu => absurd hu (Nat.not_lt_zero _)⟩)
      (P₂ := fun _ _ _ => True) (fun _ _ _ _ _ _ _ _ => trivial) fun r =>
      CGood.pure' (a := (ForInStep.yield r : ForInStep (List ℕ))) (Q := fun _ x _ _ => x = ForInStep.yield r)
        fun _ _ _ _ => rfl).weaken (fun _ _ h => h) ?_).kEq (by simp)
    · simp only [List.length_range] at hu
      simp only [List.getElem_range]
      have hpa : ∀ s v, (((ABits [a0, a1, a2] b s v ∧ z < s.next ∧ v z = eVal 0) ∧
          IndList l (2 ^ m) (bdig b m) s v) ∧ IndList nx u (bdig b (m + 1)) s v) →
          l.getD (u % l.length) 0 < s.next ∧
            v (l.getD (u % l.length) 0) = eVal (if u % l.length = bdig b m then 1 else 0) ∧
            [a0, a1, a2][m] < s.next ∧ v [a0, a1, a2][m] = kVal (if b m then 1 else 0) := by
        intro s v h
        obtain ⟨⟨⟨⟨-, haw, hav⟩, -, -⟩, ⟨hll, hlw, hlv⟩⟩, -⟩ := h
        have hpos : 0 < l.length := by rw [hll]; positivity
        have hmod := Nat.mod_lt u hpos
        refine ⟨hlw _ (getD_mem hmod), hlv _ (by rw [← hll]; exact hmod), ?_, ?_⟩
        · rw [getElem_eq_getD]; exact haw _ (getD_mem (by simp; omega))
        · rw [getElem_eq_getD]; exact hav m hm
      have hlen : ∀ s v, (((ABits [a0, a1, a2] b s v ∧ z < s.next ∧ v z = eVal 0) ∧
          IndList l (2 ^ m) (bdig b m) s v) ∧ IndList nx u (bdig b (m + 1)) s v) → l.length = 2 ^ m :=
        fun _ _ h => h.1.2.1
      split_ifs with hun
      · refine (CGood.bind ((mulKAdd_cgood _ _ _).pre fun s v h => ?_)
          (P₂ := fun _ _ _ => True) (fun _ _ _ _ _ _ _ _ => trivial) fun q =>
          CGood.pure' (Q := fun _ x _ _ => x = .yield (nx ++ [q])) fun _ _ _ _ => rfl).weaken (fun _ _ h => h) ?_
        · obtain ⟨h1, h2, h3, h4⟩ := hpa s v h
          exact ⟨wires3 h1 h3 h1, by rw [h2]; exact eVal_three _, kVal_isK h4, by rw [h2]; exact eVal_three _⟩
        · rintro s r s' v hs hP he ⟨q, s1, -, he2, -, ⟨hq, hqv⟩, -, -, -, -, -, rfl⟩
          obtain ⟨h1, h2, h3, h4⟩ := hpa s v hP
          have hll := hlen s v hP
          refine ⟨_, rfl, ⟨⟨hP.1.1.1.mono he, lt_of_lt_of_le hP.1.1.2.1 he.next, hP.1.1.2.2⟩,
            hP.1.2.mono he⟩, ind_step nx u _ q s' v _ (hP.2.mono he) (lt_of_lt_of_le hq he2.next)
            (hqv.trans (ind_mul _ _ z v _ (b m) h2 h4 hP.1.1.2.2).1) ?_⟩
          rw [hll] at hun ⊢
          have := ind_idx u (2 ^ m) (bdig b m) (b m) (bdig_lt b m) (by rw [← hll]; exact hu)
          simp only [bdig]
          rw [this]
          simp [hun]
      · refine (CGood.bind ((mulKAdd_cgood _ _ _).pre fun s v h => ?_)
          (P₂ := fun _ _ _ => True) (fun _ _ _ _ _ _ _ _ => trivial) fun q =>
          CGood.pure' (Q := fun _ x _ _ => x = .yield (nx ++ [q])) fun _ _ _ _ => rfl).weaken (fun _ _ h => h) ?_
        · obtain ⟨h1, h2, h3, h4⟩ := hpa s v h
          exact ⟨wires3 h1 h3 h.1.1.2.1, by rw [h2]; exact eVal_three _, kVal_isK h4,
            by rw [h.1.1.2.2]; exact eVal_three _⟩
        · rintro s r s' v hs hP he ⟨q, s1, -, he2, -, ⟨hq, hqv⟩, -, -, -, -, -, rfl⟩
          obtain ⟨h1, h2, h3, h4⟩ := hpa s v hP
          have hll := hlen s v hP
          refine ⟨_, rfl, ⟨⟨hP.1.1.1.mono he, lt_of_lt_of_le hP.1.1.2.1 he.next, hP.1.1.2.2⟩,
            hP.1.2.mono he⟩, ind_step nx u _ q s' v _ (hP.2.mono he) (lt_of_lt_of_le hq he2.next)
            (hqv.trans (ind_mul _ _ z v _ (b m) h2 h4 hP.1.1.2.2).2) ?_⟩
          rw [hll] at hun ⊢
          have := ind_idx u (2 ^ m) (bdig b m) (b m) (bdig_lt b m) (by rw [← hll]; exact hu)
          simp only [bdig]
          rw [this]
          cases hb : b m <;> simp [hun]
    · rintro s r s2 v hs - - ⟨r', s1, -, he, -, ⟨⟨hctx, hl⟩, hr'⟩, rfl⟩
      refine ⟨r', rfl, ⟨hctx.1.mono he, lt_of_lt_of_le hctx.2.1 he.next, hctx.2.2⟩, ?_⟩
      have := hr'.mono he
      rw [List.length_range, hl.1, ← pow_succ'] at this
      exact this
  · rintro s r s4 v hs - - ⟨o, s1, -, -, -, -, z, s2, -, -, -, -, r', s3, -, he, -, ⟨-, hl⟩, rfl⟩
    exact hl.mono he

end

/-! Chains. -/

/-- The public parameter's two words on wires `pp`. -/
def PPw (pp : List ℕ) (p : Words.Dig) (s : State) (v : Val) : Prop :=
  pp.length = 2 ∧ Wires pp s ∧ v (pp.getD 0 0) = kw p.1 ∧ v (pp.getD 1 0) = kw p.2

theorem PPw.mono {pp : List ℕ} {p : Words.Dig} {s s' : State} {v : Val} (h : PPw pp p s v) (he : Ext s s') :
    PPw pp p s' v :=
  ⟨h.1, h.2.1.mono he, h.2.2⟩

theorem PPw.eq {pp : List ℕ} {p : Words.Dig} {s : State} {v : Val} (h : PPw pp p s v) :
    pp = [pp.getD 0 0, pp.getD 1 0] := by
  obtain ⟨hl, -⟩ := h
  match pp, hl with
  | [a, b], _ => rfl

theorem PPw.map {pp : List ℕ} {p : Words.Dig} {s : State} {v : Val} (h : PPw pp p s v) :
    pp.map (w64 v) = [p.1, p.2] := by
  rw [h.eq]; simp only [List.map_cons, List.map_nil]; rw [w64_kw h.2.2.1, w64_kw h.2.2.2]

theorem PPw.isK {pp : List ℕ} {p : Words.Dig} {s : State} {v : Val} (h : PPw pp p s v) :
    ∀ w ∈ pp, v w = kVal (v w 0) := by
  rw [h.eq]
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact kw_isK h.2.2.1
  · exact kw_isK h.2.2.2

/-- A digest's first three words in an `E` wire's limbs. -/
noncomputable def cv (C : Fin 4 → Words.W) : Fin 4 → K :=
  ![ofWord (C 0).toNat, ofWord (C 1).toNat, ofWord (C 2).toNat, 0]

/-- The value at position `m` of a chain started at position `x` from `T`. -/
def cpos (i e : ℕ) (p T : Words.Dig) (x m : ℕ) : Words.Dig :=
  (List.range' x (m - x)).foldl (fun v s => Words.chainStep i s e p v) T

theorem cpos_self (i e : ℕ) (p T : Words.Dig) (x : ℕ) : cpos i e p T x x = T := by
  simp [cpos]

theorem cpos_succ (i e : ℕ) (p T : Words.Dig) (x m : ℕ) (h : x ≤ m) :
    cpos i e p T x (m + 1) = Words.chainStep i m e p (cpos i e p T x m) := by
  simp only [cpos]
  rw [show m + 1 - x = (m - x) + 1 by omega, List.range'_concat, List.foldl_append]
  simp [show x + (m - x) = m by omega]

theorem tw_bound (ty pos : ℕ) (hty : ty < 256) (hpos : pos < 2 ^ 32) : Circuit.tweak0 ty pos < 2 ^ 64 := by
  unfold Circuit.tweak0
  have h1 : (2 : ℕ) ^ 8 = 256 := by norm_num
  have h2 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  have h3 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
  rw [h1, h2, h3]
  rw [h2] at hpos
  omega

/-- The words a tweak hash of `payload` on wires hashes. -/
theorem th_words (ty pos e : ℕ) (p : Words.Dig) (idx : ℕ) (pp payload : List ℕ) (v : Val) {s : State}
    (hidx : v idx = kw (Words.tweak1 e)) (hpp : PPw pp p s v) :
    Words.tweak0 ty pos :: (idx :: pp ++ payload).map (w64 v) =
      [Words.tweak0 ty pos, Words.tweak1 e, p.1, p.2] ++ payload.map (w64 v) := by
  simp [List.map_append, hpp.map, w64_kw hidx]

theorem dVal_th (ty pos e : ℕ) (p : Words.Dig) (ws : List Words.W) :
    (digest (hashWords ([Words.tweak0 ty pos, Words.tweak1 e, p.1, p.2] ++ ws)) 0,
      digest (hashWords ([Words.tweak0 ty pos, Words.tweak1 e, p.1, p.2] ++ ws)) 1) = Words.th ty pos e p ws := rfl

theorem mux_val (v : Val) (ind tip cur : ℕ) (c : Prop) [Decidable c] (hi : v ind = eVal (if c then 1 else 0))
    (ht : v tip 3 = 0) (hc : v cur 3 = 0) :
    eVal (ev v ind * (ev v tip + ev v cur) + ev v cur) = if c then v tip else v cur := by
  rw [ev_of_eVal hi]
  split_ifs
  · rw [one_mul, add_assoc, ← two_mul, two_E, zero_mul, add_zero]
    exact (eVal_of_ev ht).symm
  · rw [zero_mul, zero_add]
    exact (eVal_of_ev hc).symm

section

variable {st : ℕ → Fin 4 → K}

/-- A chain's context: its index word, parameter, element and indicators. -/
def CECtx (idx tip : ℕ) (pp ind : List ℕ) (e : ℕ) (p T : Words.Dig) (x : ℕ) (s : State) (v : Val) : Prop :=
  idx < s.next ∧ v idx = kw (Words.tweak1 e) ∧ PPw pp p s v ∧ tip < s.next ∧ v tip = limbs3 T.1 T.2 0 ∧
    IndList ind 8 x s v

theorem CECtx.mono {idx tip : ℕ} {pp ind : List ℕ} {e : ℕ} {p T : Words.Dig} {x : ℕ} {s s' : State} {v : Val}
    (h : CECtx idx tip pp ind e p T x s v) (he : Ext s s') : CECtx idx tip pp ind e p T x s' v :=
  ⟨lt_of_lt_of_le h.1 he.next, h.2.1, h.2.2.1.mono he, lt_of_lt_of_le h.2.2.2.1 he.next, h.2.2.2.2.1,
    h.2.2.2.2.2.mono he⟩

theorem CECtx.hashPre {idx tip : ℕ} {pp ind : List ℕ} {e : ℕ} {p T : Words.Dig} {x : ℕ} {s : State} {v : Val}
    (h : CECtx idx tip pp ind e p T x s v) (a b : ℕ) (ha : a < s.next) (hb : b < s.next)
    (hav : v a = kVal (v a 0)) (hbv : v b = kVal (v b 0)) :
    Wires (idx :: pp ++ [a, b]) s ∧ ∀ w ∈ idx :: pp ++ [a, b], v w = kVal (v w 0) := by
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw
    rcases hw with (rfl | hw) | rfl | rfl
    · exact h.1
    · exact h.2.2.1.2.1 w hw
    · exact ha
    · exact hb
  · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw
    rcases hw with (rfl | hw) | rfl | rfl
    · exact kw_isK h.2.1
    · exact h.2.2.1.isK w hw
    · exact hav
    · exact hbv

theorem pos_bound (i j : ℕ) (hi : i < 42) (hj : j ≤ 7) : 8 * i + j < 2 ^ 32 := by
  have : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  omega

/-- A chain's loop invariant after the step at position `j`. -/
def CEInv (idx tip : ℕ) (pp ind : List ℕ) (i e : ℕ) (p T : Words.Dig) (x j cur : ℕ) (s : State) (v : Val) : Prop :=
  CECtx idx tip pp ind e p T x s v ∧ cur < s.next ∧
    ∃ C : Fin 4 → Words.W, v cur = cv C ∧ (x ≤ j → (C 0, C 1) = cpos i e p T x (j + 1))

theorem cv_three (C : Fin 4 → Words.W) : cv C 3 = 0 := rfl

theorem chainEnd_cg (i idx tip : ℕ) (pp ind : List ℕ) (e : ℕ) (p T : Words.Dig) (x : ℕ) (hi : i < 42)
    (hx : x < 8) (hpl : pp.length = 2) :
    CGood st 0 (fun s v => CECtx idx tip pp ind e p T x s v) (Circuit.chainEnd i idx tip pp ind)
      fun _ r s' v => r.1 < s'.next ∧ r.2 < s'.next ∧ v r.1 = kw (Words.chainFrom i e p x T).1 ∧
        v r.2 = kw (Words.chainFrom i e p x T).2 := by
  unfold Circuit.chainEnd
  refine CGood.seq (k₂ := 0) ((words_cg tip).pre fun s v h => ⟨h.2.2.2.1, by rw [h.2.2.2.2.1]; rfl⟩)
    (P₂ := fun a s v => CECtx idx tip pp ind e p T x s v ∧ a.1 < s.next ∧ a.2.1 < s.next ∧ v a.1 = kw T.1 ∧
      v a.2.1 = kw T.2)
    (fun s a s' v _ hp he hq => ⟨hp.mono he, hq.1.1, hq.1.2.1, by rw [hq.2.1, hp.2.2.2.2.1]; rfl,
      by rw [hq.2.2.1, hp.2.2.2.2.1]; rfl⟩) fun a => ?_
  obtain ⟨t0, t1, sn⟩ := a
  try dsimp only
  refine CGood.seq (k₂ := 0) ((tweakHash_cg 1 (8 * i) idx pp [t0, t1] (tw_bound 1 _ (by norm_num)
      (by have := pos_bound i 0 hi (by norm_num); omega)) (by simp [hpl])).pre
      fun s v h => h.1.hashPre t0 t1 h.2.1 h.2.2.1 (kw_isK h.2.2.2.1) (kw_isK h.2.2.2.2))
    (P₂ := fun d s v => CECtx idx tip pp ind e p T x s v ∧ d < s.next ∧
      v d = dVal (digest (hashWords ([Words.tweak0 1 (8 * i), Words.tweak1 e, p.1, p.2] ++ [T.1, T.2]))))
    (fun s d s' v _ hp he hq => ⟨hp.1.mono he, hq.1, by
      rw [hq.2, th_words _ _ e p idx pp [t0, t1] v hp.1.2.1 hp.1.2.2.1]
      simp only [List.map_cons, List.map_nil, w64_kw hp.2.2.2.1, w64_kw hp.2.2.2.2]⟩) fun d => ?_
  refine CGood.seq (k₂ := 0) ((dToEAndK_cgood d).pre fun s v h => h.2.1)
    (P₂ := fun a s v => CEInv idx tip pp ind i e p T x 0 a.1 s v)
    (fun s a s' v _ hp he hq => ⟨hp.1.mono he, hq.1, _, by rw [hq.2.2.1, hp.2.2]; rfl, fun h0 => by
      obtain rfl : x = 0 := by omega
      rw [cpos_succ _ _ _ _ _ _ le_rfl, cpos_self]
      simp only [Words.chainStep, Nat.add_zero]
      exact dVal_th _ _ _ _ _⟩) fun a => ?_
  obtain ⟨o, sn2⟩ := a
  try dsimp only
  refine (CGood.seq (k₂ := 0) ((forIn_cgood 0 _ (List.range' 1 6)
      (fun j cur s v => CEInv idx tip pp ind i e p T x j cur s v) ?_ o).pre fun s v h => h)
    (P₂ := fun r s v => CEInv idx tip pp ind i e p T x 6 r s v)
    (fun s r s' v _ _ _ hq => by simpa using hq) fun r => ?_).kEq (by simp)
  · intro j hj b
    simp only [List.length_range'] at hj
    try dsimp only
    rw [List.getElem_range', show 1 + 1 * j = j + 1 by omega]
    refine CGood.seq (k₂ := 0) ((add_cgood tip b).pre fun s v h => ⟨wires2 h.1.2.2.2.1 h.2.1,
      by rw [h.1.2.2.2.2.1]; rfl, by obtain ⟨C, hC, -⟩ := h.2.2; rw [hC]; rfl⟩)
      (P₂ := fun diff s v => CEInv idx tip pp ind i e p T x j b s v ∧ diff < s.next ∧
        v diff = eVal (ev v tip + ev v b))
      (fun s diff s' v _ hp he hq => ⟨⟨hp.1.mono he, lt_of_lt_of_le hp.2.1 he.next, hp.2.2⟩, hq⟩) fun diff => ?_
    refine CGood.seq (k₂ := 0) ((mulAdd_cgood (ind.getD (j + 1) 0) diff b).pre fun s v h => ⟨wires3
      (h.1.1.2.2.2.2.2.2.1 _ (getD_mem (by rw [h.1.1.2.2.2.2.2.1]; omega))) h.2.1 h.1.2.1,
      by rw [h.1.1.2.2.2.2.2.2.2 _ (by omega)]; rfl, by rw [h.2.2]; rfl,
      by obtain ⟨C, hC, -⟩ := h.1.2.2; rw [hC]; rfl⟩)
      (P₂ := fun m s v => CECtx idx tip pp ind e p T x s v ∧ m < s.next ∧ ∃ X : Words.Dig,
        v m 0 = ofWord X.1.toNat ∧ v m 1 = ofWord X.2.toNat ∧ v m 3 = 0 ∧ (x ≤ j + 1 → X = cpos i e p T x (j + 1)))
      (fun s m s' v _ hp he hq => by
        obtain ⟨⟨hc, hb, C, hC, hCx⟩, hd, hdv⟩ := hp
        obtain ⟨hm, hmv⟩ := hq
        refine ⟨hc.mono he, hm, ?_⟩
        rw [ev_of_eVal hdv, mux_val v _ tip b (j + 1 = x) (hc.2.2.2.2.2.2.2 _ (by omega))
          (by rw [hc.2.2.2.2.1]; rfl) (by rw [hC]; rfl)] at hmv
        by_cases hjx : j + 1 = x
        · rw [if_pos hjx, hc.2.2.2.2.1] at hmv
          refine ⟨T, by rw [hmv]; rfl, by rw [hmv]; rfl, by rw [hmv]; rfl, fun _ => ?_⟩
          rw [← hjx, cpos_self]
        · rw [if_neg hjx, hC] at hmv
          refine ⟨(C 0, C 1), by rw [hmv]; rfl, by rw [hmv]; rfl, by rw [hmv]; rfl, fun hxj => hCx (by omega)⟩)
      fun m => ?_
    refine CGood.seq (k₂ := 0) ((words_cg m).pre fun s v h => ⟨h.2.1, by obtain ⟨X, -, -, h3, -⟩ := h.2.2; exact h3⟩)
      (P₂ := fun a s v => CECtx idx tip pp ind e p T x s v ∧ a.1 < s.next ∧ a.2.1 < s.next ∧ ∃ X : Words.Dig,
        v a.1 = kw X.1 ∧ v a.2.1 = kw X.2 ∧ (x ≤ j + 1 → X = cpos i e p T x (j + 1)))
      (fun s a s' v _ hp he hq => by
        obtain ⟨hc, -, X, h0, h1, -, hX⟩ := hp
        exact ⟨hc.mono he, hq.1.1, hq.1.2.1, X, by rw [hq.2.1, h0]; rfl, by rw [hq.2.2.1, h1]; rfl, hX⟩)
      fun a => ?_
    obtain ⟨v0, v1, sn3⟩ := a
    try dsimp only
    refine CGood.seq (k₂ := 0) ((tweakHash_cg 1 (8 * i + (j + 1)) idx pp [v0, v1] (tw_bound 1 _ (by norm_num)
        (pos_bound i (j + 1) hi (by omega))) (by simp [hpl])).pre fun s v h => by
          obtain ⟨hc, h0, h1, X, hX0, hX1, -⟩ := h
          exact hc.hashPre v0 v1 h0 h1 (kw_isK hX0) (kw_isK hX1))
      (P₂ := fun d s v => CECtx idx tip pp ind e p T x s v ∧ d < s.next ∧ ∃ X : Words.Dig,
        v d = dVal (digest (hashWords ([Words.tweak0 1 (8 * i + (j + 1)), Words.tweak1 e, p.1, p.2] ++
          [X.1, X.2]))) ∧ (x ≤ j + 1 → X = cpos i e p T x (j + 1)))
      (fun s d s' v _ hp he hq => by
        obtain ⟨hc, -, -, X, hX0, hX1, hX⟩ := hp
        refine ⟨hc.mono he, hq.1, X, ?_, hX⟩
        rw [hq.2, th_words _ _ e p idx pp [v0, v1] v hc.2.1 hc.2.2.1]
        simp only [List.map_cons, List.map_nil, w64_kw hX0, w64_kw hX1]) fun d => ?_
    refine CGood.seq (k₂ := 0) ((dToEAndK_cgood d).pre fun s v h => h.2.1)
      (P₂ := fun a s v => CEInv idx tip pp ind i e p T x (j + 1) a.1 s v)
      (fun s a s' v _ hp he hq => by
        obtain ⟨hc, -, X, hXv, hX⟩ := hp
        refine ⟨hc.mono he, hq.1, _, by rw [hq.2.2.1, hXv]; rfl, fun hxj => ?_⟩
        rw [cpos_succ _ _ _ _ _ _ hxj, ← hX hxj]
        exact dVal_th _ _ _ _ _) fun a => ?_
    obtain ⟨o', sn4⟩ := a
    try dsimp only
    exact CGood.pure' fun _ _ _ h => ⟨o', rfl, h⟩
  · try dsimp only
    refine CGood.seq (k₂ := 0) ((add_cgood tip r).pre fun s v h => ⟨wires2 h.1.2.2.2.1 h.2.1,
      by rw [h.1.2.2.2.2.1]; rfl, by obtain ⟨C, hC, -⟩ := h.2.2; rw [hC]; rfl⟩)
      (P₂ := fun diff s v => CEInv idx tip pp ind i e p T x 6 r s v ∧ diff < s.next ∧
        v diff = eVal (ev v tip + ev v r))
      (fun s diff s' v _ hp he hq => ⟨⟨hp.1.mono he, lt_of_lt_of_le hp.2.1 he.next, hp.2.2⟩, hq⟩) fun diff => ?_
    refine CGood.seq (k₂ := 0) ((mulAdd_cgood (ind.getD 7 0) diff r).pre fun s v h => ⟨wires3
      (h.1.1.2.2.2.2.2.2.1 _ (getD_mem (by rw [h.1.1.2.2.2.2.2.1]; omega))) h.2.1 h.1.2.1,
      by rw [h.1.1.2.2.2.2.2.2.2 _ (by omega)]; rfl, by rw [h.2.2]; rfl,
      by obtain ⟨C, hC, -⟩ := h.1.2.2; rw [hC]; rfl⟩)
      (P₂ := fun m s v => m < s.next ∧ v m 0 = ofWord (cpos i e p T x 7).1.toNat ∧
        v m 1 = ofWord (cpos i e p T x 7).2.toNat ∧ v m 3 = 0)
      (fun s m s' v _ hp he hq => by
        obtain ⟨⟨hc, hb, C, hC, hCx⟩, hd, hdv⟩ := hp
        obtain ⟨hm, hmv⟩ := hq
        refine ⟨hm, ?_⟩
        rw [ev_of_eVal hdv, mux_val v _ tip r (7 = x) (hc.2.2.2.2.2.2.2 _ (by omega))
          (by rw [hc.2.2.2.2.1]; rfl) (by rw [hC]; rfl)] at hmv
        by_cases hjx : 7 = x
        · rw [if_pos hjx, hc.2.2.2.2.1] at hmv
          rw [hmv, ← hjx, cpos_self]
          exact ⟨rfl, rfl, rfl⟩
        · rw [if_neg hjx, hC] at hmv
          have h7 := hCx (by omega)
          rw [hmv, ← h7]
          exact ⟨rfl, rfl, rfl⟩)
      fun m => ?_
    refine CGood.seq (k₂ := 0) ((words_cg m).pre fun s v h => ⟨h.1, h.2.2.2⟩)
      (P₂ := fun a s v => a.1 < s.next ∧ a.2.1 < s.next ∧ v a.1 = kw (cpos i e p T x 7).1 ∧
        v a.2.1 = kw (cpos i e p T x 7).2)
      (fun s a s' v _ hp he hq => ⟨hq.1.1, hq.1.2.1, by rw [hq.2.1, hp.2.1]; rfl, by rw [hq.2.2.1, hp.2.2.1]; rfl⟩)
      fun a => ?_
    obtain ⟨n0, n1, sn5⟩ := a
    try dsimp only
    exact CGood.pure' fun _ _ _ h => h

end

/-! The Merkle path. -/

theorem emb_bit (β : Bool) : emb (if β then 1 else 0) = if β then 1 else 0 := by
  cases β <;> simp [emb]

theorem ite_three (β : Bool) (a b : Fin 4 → K) (ha : a 3 = 0) (hb : b 3 = 0) :
    (if β = true then a else b) 3 = 0 := by
  cases β
  · exact hb
  · exact ha

theorem sel_left (v : Val) (cur sib bit : ℕ) (β : Bool) (hb : v bit = kVal (if β then 1 else 0))
    (hc : v cur 3 = 0) (hs : v sib 3 = 0) :
    eVal ((ev v cur + ev v sib) * emb (v bit 0) + ev v cur) = if β then v sib else v cur := by
  rw [hb, kVal_apply_zero, emb_bit]
  cases β
  · simp only [if_false, Bool.false_eq_true, mul_zero, zero_add]; exact (eVal_of_ev hc).symm
  · simp only [if_true, mul_one]
    rw [show ev v cur + ev v sib + ev v cur = ev v sib by linear_combination ev v cur * two_E]
    exact (eVal_of_ev hs).symm

theorem sel_right (v : Val) (cur sib left : ℕ) (β : Bool) (hl : v left = if β then v sib else v cur)
    (hc : v cur 3 = 0) (hs : v sib 3 = 0) :
    eVal (ev v left + (ev v cur + ev v sib)) = if β then v cur else v sib := by
  cases β
  · simp only [if_false, Bool.false_eq_true] at hl ⊢
    rw [Model.ev, hl, ← Model.ev, show ev v cur + (ev v cur + ev v sib) = ev v sib by linear_combination ev v cur * two_E]
    exact (eVal_of_ev hs).symm
  · simp only [if_true] at hl ⊢
    rw [Model.ev, hl, ← Model.ev, show ev v sib + (ev v cur + ev v sib) = ev v cur by linear_combination ev v sib * two_E]
    exact (eVal_of_ev hc).symm

section

variable {st : ℕ → Fin 4 → K}

/-- A Merkle level's context: its index word, parameter, bit and node. -/
def LCtx (idx bit node : ℕ) (pp : List ℕ) (ix : ℕ) (p : Words.Dig) (β : Bool) (D : Fin 4 → Words.W) (s : State)
    (v : Val) : Prop :=
  idx < s.next ∧ v idx = kw (Words.tweak1 ix) ∧ PPw pp p s v ∧ bit < s.next ∧
    v bit = kVal (if β then 1 else 0) ∧ node < s.next ∧ v node = dVal D

theorem LCtx.mono {idx bit node : ℕ} {pp : List ℕ} {ix : ℕ} {p : Words.Dig} {β : Bool} {D : Fin 4 → Words.W}
    {s s' : State} {v : Val} (h : LCtx idx bit node pp ix p β D s v) (he : Ext s s') :
    LCtx idx bit node pp ix p β D s' v :=
  ⟨lt_of_lt_of_le h.1 he.next, h.2.1, h.2.2.1.mono he, lt_of_lt_of_le h.2.2.2.1 he.next, h.2.2.2.2.1,
    lt_of_lt_of_le h.2.2.2.2.2.1 he.next, h.2.2.2.2.2.2⟩

/-- `level`: the parent of the node and the sibling `S`, the node on the side the bit names. -/
theorem level_cg (l idx bit node : ℕ) (pp : List ℕ) (ix : ℕ) (p S : Words.Dig) (β : Bool)
    (D : Fin 4 → Words.W) (hl : l < 32) (hpl : pp.length = 2) :
    CGood st 0 (fun s v => LCtx idx bit node pp ix p β D s v) (Circuit.level l idx bit node pp)
      fun _ r s' v => r < s'.next ∧ v r = dVal (digest (hashWords ([Words.tweak0 3 (l + 1), Words.tweak1 ix, p.1, p.2] ++
        if β then [S.1, S.2, D 0, D 1] else [D 0, D 1, S.1, S.2]))) := by
  unfold Circuit.level
  refine CGood.seq (k₂ := 0) ((dToEAndK_cgood node).pre fun s v h => h.2.2.2.2.2.1)
    (P₂ := fun a s v => LCtx idx bit node pp ix p β D s v ∧ a.1 < s.next ∧ v a.1 = cv D)
    (fun s a s' v _ hp he hq => ⟨hp.mono he, hq.1, by rw [hq.2.2.1, hp.2.2.2.2.2.2]; rfl⟩) fun a => ?_
  obtain ⟨cur, sn⟩ := a
  try dsimp only
  refine CGood.seq (k₂ := 0) ((wire_cgood (limbs3 S.1 S.2 0)).pre fun _ _ _ => trivial)
    (P₂ := fun sib s v => LCtx idx bit node pp ix p β D s v ∧ cur < s.next ∧ v cur = cv D ∧ sib < s.next ∧
      v sib = limbs3 S.1 S.2 0)
    (fun s sib s' v _ hp he hq => ⟨hp.1.mono he, lt_of_lt_of_le hp.2.1 he.next, hp.2.2,
      by rw [hq.2.1, hq.1]; exact Nat.lt_succ_self _, hq.2.2⟩) fun sib => ?_
  refine CGood.seq (k₂ := 0) ((add_cgood cur sib).pre fun s v h => ⟨wires2 h.2.1 h.2.2.2.1,
      by rw [h.2.2.1]; rfl, by rw [h.2.2.2.2]; rfl⟩)
    (P₂ := fun diff s v => (LCtx idx bit node pp ix p β D s v ∧ cur < s.next ∧ v cur = cv D ∧ sib < s.next ∧
      v sib = limbs3 S.1 S.2 0) ∧ diff < s.next ∧ v diff = eVal (ev v cur + ev v sib))
    (fun s diff s' v _ hp he hq => ⟨⟨hp.1.mono he, lt_of_lt_of_le hp.2.1 he.next, hp.2.2.1,
      lt_of_lt_of_le hp.2.2.2.1 he.next, hp.2.2.2.2⟩, hq⟩) fun diff => ?_
  refine CGood.seq (k₂ := 0) ((mulKAdd_cgood diff bit cur).pre fun s v h => ⟨wires3 h.2.1 h.1.1.2.2.2.1 h.1.2.1,
      by rw [h.2.2]; rfl, kVal_isK h.1.1.2.2.2.2.1, by rw [h.1.2.2.1]; rfl⟩)
    (P₂ := fun left s v => ((LCtx idx bit node pp ix p β D s v ∧ cur < s.next ∧ v cur = cv D ∧ sib < s.next ∧
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
    (P₂ := fun right s v => LCtx idx bit node pp ix p β D s v ∧ left < s.next ∧ right < s.next ∧
      v left = (if β then limbs3 S.1 S.2 0 else cv D) ∧ v right = (if β then cv D else limbs3 S.1 S.2 0))
    (fun s right s' v _ hp he hq => by
      obtain ⟨⟨⟨hc, hcur, hcv, hsib, hsv⟩, hd, hdv⟩, hl, hlv⟩ := hp
      refine ⟨hc.mono he, lt_of_lt_of_le hl he.next, hq.1, by rw [hlv, hcv, hsv], ?_⟩
      rw [hq.2, ev_of_eVal hdv, sel_right v cur sib left β hlv (by rw [hcv]; rfl) (by rw [hsv]; rfl), hcv, hsv])
    fun right => ?_
  refine CGood.seq (k₂ := 0) ((words_cg left).pre fun s v h => ⟨h.2.1, by rw [h.2.2.2.1]; split_ifs <;> rfl⟩)
    (P₂ := fun a s v => LCtx idx bit node pp ix p β D s v ∧ right < s.next ∧
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
    (P₂ := fun a s v => LCtx idx bit node pp ix p β D s v ∧ l0 < s.next ∧ l1 < s.next ∧
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
  refine ((tweakHash_cg 3 (l + 1) idx pp [l0, l1, r0, r1] (tw_bound 3 _ (by norm_num)
      (by have : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
          omega)) (by simp [hpl])).pre fun s v h => ?_).weaken (fun _ _ h => h) ?_
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
    rw [hrv, th_words _ _ ix p idx pp [l0, l1, r0, r1] v hc.2.1 hc.2.2.1]
    simp only [List.map_cons, List.map_nil, w64_kw h0v, w64_kw h1v, w64_kw h2v, w64_kw h3v]
    cases β <;> rfl

end

/-! Digits, word lists, chains' ends and the climb. -/

theorem mod8_bits (n : ℕ) : n % 8 = (if n.testBit 0 then 1 else 0) + (if n.testBit 1 then 2 else 0) +
    (if n.testBit 2 then 4 else 0) := by
  simp only [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq, pow_zero, pow_one, Nat.div_one,
    show (2 : ℕ) ^ 2 = 4 from rfl]
  split_ifs <;> omega

theorem digit_bits (w : Words.W) (r : ℕ) : Words.digit w r =
    (if w.toNat.testBit (3 * r) then 1 else 0) + (if w.toNat.testBit (3 * r + 1) then 2 else 0) +
      (if w.toNat.testBit (3 * r + 2) then 4 else 0) := by
  rw [Words.digit, mod8_bits]
  simp only [Nat.testBit_div_two_pow, Nat.zero_add, Nat.add_comm 1, Nat.add_comm 2]

/-- The 126 digit bits of a digest: its first word's low 63, then its second's. -/
def bitsB (D : Fin 4 → Words.W) (j : ℕ) : Bool :=
  if j < 63 then (D 0).toNat.testBit j else (D 1).toNat.testBit (j - 63)

theorem dig_three (B : ℕ → Bool) (i : ℕ) : dig B i 3 =
    (if B (3 * i) then 1 else 0) + (if B (3 * i + 1) then 2 else 0) + (if B (3 * i + 2) then 4 else 0) := by
  simp [dig, List.range_succ]
  ring

theorem dig_eq (D : Fin 4 → Words.W) (i : ℕ) (hi : i < 42) :
    dig (bitsB D) i 3 = Words.digit (if i < 21 then D 0 else D 1) (i % 21) := by
  rw [dig_three, digit_bits]
  by_cases h21 : i < 21
  · simp only [bitsB, if_pos h21, Nat.mod_eq_of_lt h21, if_pos (show 3 * i < 63 by omega),
      if_pos (show 3 * i + 1 < 63 by omega), if_pos (show 3 * i + 2 < 63 by omega)]
  · have hm : i % 21 = i - 21 := by rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    simp only [bitsB, if_neg h21, hm, if_neg (show ¬(3 * i < 63) by omega),
      if_neg (show ¬(3 * i + 1 < 63) by omega), if_neg (show ¬(3 * i + 2 < 63) by omega),
      show 3 * i - 63 = 3 * (i - 21) by omega, show 3 * i + 1 - 63 = 3 * (i - 21) + 1 by omega,
      show 3 * i + 2 - 63 = 3 * (i - 21) + 2 by omega]

theorem psum_eq (D : Fin 4 → Words.W) : psum (bitsB D) 42 = (Words.digits (D 0, D 1)).sum := by
  rw [psum, Words.digits]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact dig_eq D i (List.mem_range.mp hi)

theorem digits_getD (D : Fin 4 → Words.W) (i : ℕ) (hi : i < 42) :
    (Words.digits (D 0, D 1)).getD i 0 = dig (bitsB D) i 3 := by
  rw [dig_eq D i hi, Words.digits, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem bdig_three (b : ℕ → Bool) : bdig b 3 =
    (if b 0 then 1 else 0) + (if b 1 then 2 else 0) + (if b 2 then 4 else 0) := by
  simp [bdig]

/-- Wires `ws` carrying the words `xs`. -/
def LW (ws : List ℕ) (xs : List Words.W) (s : State) (v : Val) : Prop :=
  ws.length = xs.length ∧ Wires ws s ∧ ∀ i < ws.length, v (ws.getD i 0) = kw (xs.getD i 0)

theorem LW.mono {ws : List ℕ} {xs : List Words.W} {s s' : State} {v : Val} (h : LW ws xs s v) (he : Ext s s') :
    LW ws xs s' v :=
  ⟨h.1, h.2.1.mono he, h.2.2⟩

theorem LW.map {ws : List ℕ} {xs : List Words.W} {s : State} {v : Val} (h : LW ws xs s v) :
    ws.map (w64 v) = xs := by
  apply List.ext_getElem
  · simp [h.1]
  · intro i h1 h2
    simp only [List.getElem_map]
    have := h.2.2 i (by simpa using h1)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1), Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some] at this
    exact w64_kw this

theorem LW.isK {ws : List ℕ} {xs : List Words.W} {s : State} {v : Val} (h : LW ws xs s v) :
    ∀ w ∈ ws, v w = kVal (v w 0) := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
  have := h.2.2 i hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
  exact kw_isK this

theorem LW.append {a b : List ℕ} {xs ys : List Words.W} {s : State} {v : Val} (ha : LW a xs s v)
    (hb : LW b ys s v) : LW (a ++ b) (xs ++ ys) s v := by
  refine ⟨by simp [ha.1, hb.1], fun w hw => ?_, fun i hi => ?_⟩
  · rcases List.mem_append.mp hw with hw | hw
    · exact ha.2.1 w hw
    · exact hb.2.1 w hw
  · simp only [List.length_append] at hi
    by_cases hil : i < a.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hil, ← List.getD_eq_getElem?_getD, ha.2.2 i hil,
        List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [← ha.1]; exact hil)]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), ← List.getD_eq_getElem?_getD,
        hb.2.2 _ (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by rw [← ha.1]; omega), ha.1]

theorem LW.ppw {pp : List ℕ} {p : Words.Dig} {s : State} {v : Val} (h : LW pp [p.1, p.2] s v) : PPw pp p s v :=
  ⟨h.1, h.2.1, h.2.2 0 (by rw [h.1]; simp), h.2.2 1 (by rw [h.1]; simp)⟩

theorem map_val_finRange (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2; simp

theorem ofFn_eq_range {α : Type} (n : ℕ) (F : ℕ → α) : (List.ofFn fun i : Fin n => F i.val) = (List.range n).map F := by
  rw [List.ofFn_eq_map, ← map_val_finRange, List.map_map]
  rfl

theorem foldl_finRange {α : Type} (n : ℕ) (F : α → ℕ → α) (x : α) :
    (List.finRange n).foldl (fun c l => F c l.val) x = (List.range n).foldl F x := by
  rw [← map_val_finRange, List.foldl_map]

/-- A signature's path element `l`, zero past 32. -/
def pathN (sig : Words.Sig) (l : ℕ) : Words.Dig := if h : l < 32 then sig.path ⟨l, h⟩ else (0, 0)

/-- A signature's chain element `i`, zero past 42. -/
def tipN (sig : Words.Sig) (i : ℕ) : Words.Dig := if h : i < 42 then sig.tips ⟨i, h⟩ else (0, 0)

/-- Chain `i`'s end from the digits `xs`. -/
def endN (e : ℕ) (p : Words.Dig) (sig : Words.Sig) (xs : List ℕ) (i : ℕ) : Words.Dig :=
  Words.chainFrom i e p (xs.getD i 0) (tipN sig i)

/-- The words of the first `i` chains' ends. -/
def endsW (e : ℕ) (p : Words.Dig) (sig : Words.Sig) (xs : List ℕ) (i : ℕ) : List Words.W :=
  (List.range i).flatMap fun i' => [(endN e p sig xs i').1, (endN e p sig xs i').2]

theorem endsW_succ (e : ℕ) (p : Words.Dig) (sig : Words.Sig) (xs : List ℕ) (i : ℕ) :
    endsW e p sig xs (i + 1) = endsW e p sig xs i ++ [(endN e p sig xs i).1, (endN e p sig xs i).2] := by
  simp [endsW, List.range_succ, List.flatMap_append]

theorem leaf_eq (e : ℕ) (p : Words.Dig) (sig : Words.Sig) (xs : List ℕ) :
    Words.leaf e p (List.ofFn fun i : Fin 42 => Words.chainFrom i e p (xs.getD i 0) (sig.tips i)) =
      Words.th 2 0 e p (endsW e p sig xs 42) := by
  have : (List.ofFn fun i : Fin 42 => Words.chainFrom i e p (xs.getD i 0) (sig.tips i)) =
      List.ofFn fun i : Fin 42 => endN e p sig xs i.val := by
    congr 1
    funext i
    simp [endN, tipN, i.isLt]
  rw [this, ofFn_eq_range, Words.leaf, endsW, List.flatMap_map]

/-- The path climbed `l` levels from `lf`. -/
def climbN (e : ℕ) (p : Words.Dig) (sig : Words.Sig) (lf : Words.Dig) (l : ℕ) : Words.Dig :=
  (List.range l).foldl (fun cur l => Words.parent e l p cur (pathN sig l)) lf

theorem climbN_succ (e : ℕ) (p : Words.Dig) (sig : Words.Sig) (lf : Words.Dig) (l : ℕ) :
    climbN e p sig lf (l + 1) = Words.parent e l p (climbN e p sig lf l) (pathN sig l) := by
  simp [climbN, List.range_succ]

theorem climb_eq (e : ℕ) (p : Words.Dig) (sig : Words.Sig) (lf : Words.Dig) :
    Words.climb e p sig.path lf = climbN e p sig lf 32 := by
  have hf : (fun cur (l : Fin 32) => Words.parent e l.val p cur (sig.path l)) =
      fun c (l : Fin 32) => (fun cur l => Words.parent e l p cur (pathN sig l)) c l.val := by
    funext cur l; simp only [pathN, dif_pos l.isLt]
  unfold Words.climb
  rw [hf]
  exact foldl_finRange 32 (fun cur l => Words.parent e l p cur (pathN sig l)) lf

section

variable {st : ℕ → Fin 4 → K}

theorem sw_lw1 {ws : List ℕ} {a b c : Words.W} {s : State} {v : Val}
    (h : ws.length = 3 - 1 ∧ Wires ws s ∧ ∀ i < 3 - 1, v (ws.getD i 0) = kw ([a, b, c].getD i 0)) :
    LW ws [a, b] s v := by
  refine ⟨h.1, h.2.1, fun i hi => ?_⟩
  rw [h.1] at hi
  rw [h.2.2 i hi]
  interval_cases i <;> rfl

theorem sw_lw2 {ws : List ℕ} {a b c : Words.W} {s : State} {v : Val}
    (h : ws.length = 3 - 2 ∧ Wires ws s ∧ ∀ i < 3 - 2, v (ws.getD i 0) = kw ([a, b, c].getD i 0)) :
    LW ws [a] s v := by
  refine ⟨h.1, h.2.1, fun i hi => ?_⟩
  rw [h.1] at hi
  rw [h.2.2 i hi]
  interval_cases i; rfl

theorem hashPre_of {idx : ℕ} {pp pl : List ℕ} {xs ys : List Words.W} {s : State} {v : Val} {t : Words.W}
    (hidx : idx < s.next) (hv : v idx = kw t) (hpp : LW pp xs s v) (hpl : LW pl ys s v) :
    Wires (idx :: pp ++ pl) s ∧ ∀ w ∈ idx :: pp ++ pl, v w = kVal (v w 0) := by
  have h := hpp.append hpl
  refine ⟨wires_cons.2 ⟨hidx, h.2.1⟩, fun w hw => ?_⟩
  rcases List.mem_cons.mp hw with rfl | hw
  · exact kw_isK hv
  · exact h.isK w hw

theorem endsW_length (e : ℕ) (p : Words.Dig) (sig : Words.Sig) (xs : List ℕ) (i : ℕ) :
    (endsW e p sig xs i).length = 2 * i := by
  induction i with
  | zero => simp [endsW]
  | succ i ih => rw [endsW_succ, List.length_append, ih]; simp; ring

theorem kVal_dVal (D : Fin 4 → Words.W) (i : Fin 4) : kVal (dVal D i) = kw (D i) := rfl

theorem toNat_ofNat_lt (e : ℕ) (he : e < 2 ^ 32) : (BitVec.ofNat 64 e).toNat = e := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_lt_of_le he (Nat.pow_le_pow_right (by norm_num) (by norm_num)))]

theorem toWord_kw (x : Words.W) : toWord (kw x 0) = x.toNat := by
  rw [kw, kVal_apply_zero, toWord_ofWord _ x.isLt]

theorem bitK_eq (n i : ℕ) : bitK n i = if n.testBit i then 1 else 0 := rfl

theorem bitK_high (e i : ℕ) (he : e < 2 ^ 32) (hi : 32 ≤ i) : bitK e i = 0 := by
  rw [bitK, Nat.testBit_lt_two_pow (lt_of_lt_of_le he (Nat.pow_le_pow_right (by norm_num) hi))]
  rfl

/-- The digit bits' wires. -/
def DBits (db : List ℕ) (B : ℕ → Bool) (s : State) (v : Val) : Prop :=
  db.length = 126 ∧ Wires db s ∧ ∀ j < 126, v (db.getD j 0) = kVal (if B j then 1 else 0)

theorem DBits.mono {db : List ℕ} {B : ℕ → Bool} {s s' : State} {v : Val} (h : DBits db B s v) (he : Ext s s') :
    DBits db B s' v :=
  ⟨h.1, h.2.1.mono he, h.2.2⟩

theorem dbits_of (lo hi : List ℕ) (D : Fin 4 → Words.W) (s : State) (v : Val) (hlo : BitsOf lo (D 0).toNat s v)
    (hhi : BitsOf hi (D 1).toNat s v) : DBits (List.take 63 lo ++ List.take 63 hi) (bitsB D) s v := by
  obtain ⟨hl, hlw, hlv⟩ := hlo
  obtain ⟨hh, hhw, hhv⟩ := hhi
  refine ⟨by simp [hl, hh], fun w hw => ?_, fun j hj => ?_⟩
  · rcases List.mem_append.mp hw with hw | hw
    · exact hlw w (List.mem_of_mem_take hw)
    · exact hhw w (List.mem_of_mem_take hw)
  · by_cases hj63 : j < 63
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hl]; omega), List.getElem?_take,
        if_pos hj63, ← List.getD_eq_getElem?_getD, hlv j (by omega), bitK_eq]
      simp [bitsB, hj63]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hl]; omega), List.getElem?_take]
      simp only [List.length_take, hl, show min 63 64 = 63 from rfl]
      rw [if_pos (by omega), ← List.getD_eq_getElem?_getD, hhv _ (by omega), bitK_eq]
      simp [bitsB, hj63]

/-- A signature's context after its header: statement words, zero, epoch bits and index word. -/
def SigG (j : ℕ) (p : Words.Dig) (m : Words.W × Words.W × Words.W × Words.W) (e : ℕ) (pp mlo mhi : List ℕ)
    (z : ℕ) (bits : List ℕ) (idx : ℕ) (s : State) (v : Val) : Prop :=
  s.statement = 5 * j + 4 ∧ LW pp [p.1, p.2] s v ∧ LW mlo [m.1, m.2.1] s v ∧ LW mhi [m.2.2.1, m.2.2.2] s v ∧
    z < s.next ∧ v z = kVal 0 ∧ BitsOf bits e s v ∧ idx < s.next ∧ v idx = kw (Words.tweak1 e)

theorem SigG.step {j : ℕ} {p : Words.Dig} {m : Words.W × Words.W × Words.W × Words.W} {e : ℕ}
    {pp mlo mhi : List ℕ} {z : ℕ} {bits : List ℕ} {idx : ℕ} {s s' : State} {v : Val}
    (h : SigG j p m e pp mlo mhi z bits idx s v) (he : Ext s s') (hst : s'.statement = s.statement + 0) :
    SigG j p m e pp mlo mhi z bits idx s' v :=
  ⟨by rw [hst, h.1], h.2.1.mono he, h.2.2.1.mono he, h.2.2.2.1.mono he, lt_of_lt_of_le h.2.2.2.2.1 he.next,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1.mono he, lt_of_lt_of_le h.2.2.2.2.2.2.2.1 he.next, h.2.2.2.2.2.2.2.2⟩

end

section

variable {st : ℕ → Fin 4 → K}

theorem lw1 {a : ℕ} {x : Words.W} {s : State} {v : Val} (ha : a < s.next) (hv : v a = kw x) : LW [a] [x] s v :=
  ⟨rfl, wires_cons.2 ⟨ha, wires_nil⟩, fun i hi => by
    have : i = 0 := by simpa using hi
    subst this; exact hv⟩

theorem lw2 {a b : ℕ} {x y : Words.W} {s : State} {v : Val} (ha : a < s.next) (hb : b < s.next)
    (hav : v a = kw x) (hbv : v b = kw y) : LW [a, b] [x, y] s v :=
  ⟨rfl, wires2 ha hb, fun i hi => by
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i
    · exact hav
    · exact hbv⟩

theorem lw3 {a b c : ℕ} {x y z : Words.W} {s : State} {v : Val} (ha : a < s.next) (hb : b < s.next)
    (hc : c < s.next) (hav : v a = kw x) (hbv : v b = kw y) (hcv : v c = kw z) : LW [a, b, c] [x, y, z] s v :=
  ⟨rfl, wires3 ha hb hc, fun i hi => by
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i
    · exact hav
    · exact hbv
    · exact hcv⟩

/-- The header's statement words. -/
def Hdr (p : Words.Dig) (m : Words.W × Words.W × Words.W × Words.W) (pp mlo mhi : List ℕ) (s : State) (v : Val) :
    Prop :=
  LW pp [p.1, p.2] s v ∧ LW mlo [m.1, m.2.1] s v ∧ LW mhi [m.2.2.1, m.2.2.2] s v

theorem Hdr.mono {p : Words.Dig} {m : Words.W × Words.W × Words.W × Words.W} {pp mlo mhi : List ℕ}
    {s s' : State} {v : Val} (h : Hdr p m pp mlo mhi s v) (he : Ext s s') : Hdr p m pp mlo mhi s' v :=
  ⟨h.1.mono he, h.2.1.mono he, h.2.2.mono he⟩

theorem signature_cg (j : ℕ) (p rt : Words.Dig) (m : Words.W × Words.W × Words.W × Words.W) (e : ℕ)
    (sig : Words.Sig) (henc : Encodes st j p rt m e) (hver : Words.verify p rt m e sig = true) :
    CGood st 5 (fun s _ => s.statement = 5 * j) Circuit.signature fun _ _ _ _ => True := by
  obtain ⟨he32, h0, h1, h2, h3, h4⟩ := henc
  set Dfull : Fin 4 → Words.W := digest (hashWords ([Words.tweak0 4 0, Words.tweak1 e, p.1, p.2] ++
    [m.1, m.2.1, m.2.2.1, m.2.2.2, sig.rho.1, sig.rho.2.1, sig.rho.2.2, 0])) with hD
  have key : ∃ xs, Words.encode p m sig.rho e = some xs ∧
      Words.climb e p sig.path (Words.leaf e p (List.ofFn fun i : Fin 42 =>
        Words.chainFrom i e p (xs.getD i 0) (sig.tips i))) = rt := by
    cases h : Words.encode p m sig.rho e with
    | none => simp [Words.verify, h] at hver
    | some xs =>
      simp only [Words.verify, h, Option.elim_some] at hver
      exact ⟨xs, rfl, beq_iff_eq.mp hver⟩
  obtain ⟨xs, hxs, hcl⟩ := key
  have hcond : (Dfull 0).getLsbD 63 = false ∧ (Dfull 1).getLsbD 63 = false ∧
      (Words.digits (Dfull 0, Dfull 1)).sum = 195 ∧ xs = Words.digits (Dfull 0, Dfull 1) := by
    unfold Words.encode at hxs
    dsimp only at hxs
    split_ifs at hxs with hc
    exact ⟨hc.1, hc.2.1, hc.2.2, (Option.some.inj hxs).symm⟩
  obtain ⟨h63a, h63b, hsum, rfl⟩ := hcond
  set x := Words.digits (Dfull 0, Dfull 1) with hx
  set L := Words.th 2 0 e p (endsW e p sig x 42) with hL
  have hroot : climbN e p sig L 32 = rt := by
    rw [hL, ← leaf_eq, ← climb_eq]; exact hcl
  unfold Circuit.signature
  refine CGood.seq (k₂ := 4) ((statementWords_cg 1 p.1 p.2 0 (Or.inl ⟨rfl, rfl⟩)).stmt.pre
      fun s _ h => by rw [h]; exact h0)
    (P₂ := fun pp s v => s.statement = 5 * j + 1 ∧ LW pp [p.1, p.2] s v)
    (fun s a s' v _ hp he hq => ⟨by rw [hq.2, hp], sw_lw1 hq.1⟩) fun pp => ?_
  refine CGood.seq (k₂ := 3) ((statementWords_cg 1 m.1 m.2.1 0 (Or.inl ⟨rfl, rfl⟩)).stmt.pre
      fun s _ h => by rw [h.1]; exact h1)
    (P₂ := fun mlo s v => s.statement = 5 * j + 2 ∧ LW pp [p.1, p.2] s v ∧ LW mlo [m.1, m.2.1] s v)
    (fun s a s' v _ hp he hq => ⟨by rw [hq.2, hp.1], hp.2.mono he, sw_lw1 hq.1⟩) fun mlo => ?_
  refine CGood.seq (k₂ := 2) ((statementWords_cg 1 m.2.2.1 m.2.2.2 0 (Or.inl ⟨rfl, rfl⟩)).stmt.pre
      fun s _ h => by rw [h.1]; exact h2)
    (P₂ := fun mhi s v => s.statement = 5 * j + 3 ∧ Hdr p m pp mlo mhi s v)
    (fun s a s' v _ hp he hq => ⟨by rw [hq.2, hp.1], hp.2.1.mono he, hp.2.2.mono he, sw_lw1 hq.1⟩) fun mhi => ?_
  refine CGood.seq (k₂ := 1) ((statementWords_cg 2 (BitVec.ofNat 64 e) 0 0 (Or.inr ⟨rfl, rfl, rfl⟩)).stmt.pre
      fun s _ h => by rw [h.1]; exact h3)
    (P₂ := fun ep s v => s.statement = 5 * j + 4 ∧ Hdr p m pp mlo mhi s v ∧ LW ep [BitVec.ofNat 64 e] s v)
    (fun s a s' v _ hp he hq => ⟨by rw [hq.2, hp.1], hp.2.mono he, sw_lw2 hq.1⟩) fun ep => ?_
  refine CGood.seq (k₂ := 1) ((kConst_cgood 0).stmt.pre fun _ _ _ => trivial)
    (P₂ := fun z s v => (s.statement = 5 * j + 4 ∧ Hdr p m pp mlo mhi s v ∧ LW ep [BitVec.ofNat 64 e] s v) ∧
      z < s.next ∧ v z = kVal 0)
    (fun s a s' v _ hp he hq => ⟨⟨by rw [hq.2, hp.1], hp.2.1.mono he, hp.2.2.mono he⟩, hq.1.1,
      by rw [hq.1.2, ofWord_zero]⟩) fun z => ?_
  have hep : ∀ s v, LW ep [BitVec.ofNat 64 e] s v → ep.getD 0 0 < s.next ∧
      v (ep.getD 0 0) = kw (BitVec.ofNat 64 e) := fun s v h =>
    ⟨h.2.1 _ (getD_mem (by rw [h.1]; simp)), h.2.2 0 (by rw [h.1]; simp)⟩
  refine CGood.seq (k₂ := 1) ((split_cgood (ep.getD 0 0)).stmt.pre fun s v h =>
      ⟨(hep s v h.1.2.2).1, kw_isK (hep s v h.1.2.2).2⟩)
    (P₂ := fun bits s v => s.statement = 5 * j + 4 ∧ Hdr p m pp mlo mhi s v ∧ z < s.next ∧ v z = kVal 0 ∧
      BitsOf bits e s v)
    (fun s a s' v _ hp he hq => ⟨by rw [hq.2, hp.1.1], hp.1.2.1.mono he, lt_of_lt_of_le hp.2.1 he.next, hp.2.2,
      hq.1.1, hq.1.2.1, fun i hi => by
        rw [hq.1.2.2 i hi, (hep s v hp.1.2.2).2, toWord_kw, toNat_ofNat_lt e he32]⟩) fun bits => ?_
  refine CGood.seq (k₂ := 1) ((forIn_unit_cgood (bits.drop 32) (fun k => eqConstK k 0)
      (fun s v => Hdr p m pp mlo mhi s v ∧ z < s.next ∧ v z = kVal 0 ∧ BitsOf bits e s v)
      (fun _ _ _ h he => ⟨h.1.mono he, lt_of_lt_of_le h.2.1 he.next, h.2.2.1, h.2.2.2.mono he⟩)
      fun i hi => (eqConstK_cgood _ 0).pre fun s v h => ?_).stmt.pre fun s v h => h.2)
    (P₂ := fun _ s v => s.statement = 5 * j + 4 ∧ Hdr p m pp mlo mhi s v ∧ z < s.next ∧ v z = kVal 0 ∧
      BitsOf bits e s v)
    (fun s a s' v _ hp he hq => ⟨by rw [hq.2, hp.1], hp.2.1.mono he, lt_of_lt_of_le hp.2.2.1 he.next, hp.2.2.2.1,
      hp.2.2.2.2.mono he⟩) fun _ => ?_
  · obtain ⟨-, -, -, hbl, hbw, hbv⟩ := h
    simp only [List.length_drop, hbl] at hi
    have hget : (bits.drop 32)[i] = bits.getD (32 + i) 0 := by
      rw [List.getElem_drop, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [hget]
    exact ⟨hbw _ (getD_mem (by omega)), by rw [hbv _ (by omega), bitK_high e _ he32 (by omega), ofWord_zero]⟩
  refine CGood.seq (k₂ := 1) ((indexWord_cg bits 0 e he32 (by norm_num)).stmt.pre fun s v h => h.2.2.2.2)
    (P₂ := fun idx s v => SigG j p m e pp mlo mhi z bits idx s v)
    (fun s a s' v _ hp he hq => ⟨by rw [hq.2, hp.1], hp.2.1.1.mono he, hp.2.1.2.1.mono he, hp.2.1.2.2.mono he,
      lt_of_lt_of_le hp.2.2.1 he.next, hp.2.2.2.1, hp.2.2.2.2.mono he, hq.1.1,
      by rw [hq.1.2, pow_zero, Nat.div_one]⟩) fun idx => ?_
  refine CGood.seq (k₂ := 1) ((wire_cgood (limbs3 sig.rho.1 sig.rho.2.1 sig.rho.2.2)).stmt.pre fun _ _ _ => trivial)
    (P₂ := fun rho s v => SigG j p m e pp mlo mhi z bits idx s v ∧ rho < s.next ∧
      v rho = limbs3 sig.rho.1 sig.rho.2.1 sig.rho.2.2)
    (fun s a s' v _ hp he hq => ⟨hp.step he hq.2, by rw [hq.1.2.1, hq.1.1]; exact Nat.lt_succ_self _, hq.1.2.2⟩)
    fun rho => ?_
  refine CGood.seq (k₂ := 1) ((words_cg rho).stmt.pre fun s v h => ⟨h.2.1, by rw [h.2.2]; rfl⟩)
    (P₂ := fun a s v => SigG j p m e pp mlo mhi z bits idx s v ∧
      LW [a.1, a.2.1, a.2.2] [sig.rho.1, sig.rho.2.1, sig.rho.2.2] s v)
    (fun s a s' v _ hp he hq => ⟨hp.1.step he hq.2, lw3 hq.1.1.1 hq.1.1.2.1 hq.1.1.2.2
      (by rw [hq.1.2.1, hp.2.2]; rfl) (by rw [hq.1.2.2.1, hp.2.2]; rfl) (by rw [hq.1.2.2.2, hp.2.2]; rfl)⟩)
    fun a => ?_
  obtain ⟨r0, r1, r2⟩ := a
  try dsimp only
  refine CGood.seq (k₂ := 1) ((CGood.hyp fun hl => tweakHash_cg 4 0 idx pp (mlo ++ mhi ++ [r0, r1, r2, z])
      (tw_bound 4 0 (by norm_num) (by norm_num)) hl).stmt.pre fun s v h => ⟨by
        simp only [List.length_append, List.length_cons, List.length_nil, h.1.2.1.1, h.1.2.2.1.1, h.1.2.2.2.1.1]
        norm_num, hashPre_of h.1.2.2.2.2.2.2.2.1 h.1.2.2.2.2.2.2.2.2 h.1.2.1
          ((h.1.2.2.1.append h.1.2.2.2.1).append (h.2.append (lw1 h.1.2.2.2.2.1 (by rw [h.1.2.2.2.2.2.1, kw_zero]))))⟩)
    (P₂ := fun d s v => SigG j p m e pp mlo mhi z bits idx s v ∧ d < s.next ∧ v d = dVal Dfull)
    (fun s d s' v _ hp he hq => ⟨hp.1.step he hq.2, hq.1.1, by
      have hpl : LW (mlo ++ mhi ++ [r0, r1, r2, z])
          ([m.1, m.2.1] ++ [m.2.2.1, m.2.2.2] ++ [sig.rho.1, sig.rho.2.1, sig.rho.2.2, 0]) s v :=
        (hp.1.2.2.1.append hp.1.2.2.2.1).append (hp.2.append
          (lw1 hp.1.2.2.2.2.1 (by rw [hp.1.2.2.2.2.2.1, kw_zero])))
      rw [hq.1.2, th_words _ _ e p idx pp _ v hp.1.2.2.2.2.2.2.2.2 hp.1.2.1.ppw, hpl.map, hD]
      simp only [List.cons_append, List.nil_append]⟩)
    fun d => ?_
  refine CGood.seq (k₂ := 1) ((dToK_cgood d).stmt.pre fun s v h => h.2.1)
    (P₂ := fun ks s v => SigG j p m e pp mlo mhi z bits idx s v ∧ ks.length = 4 ∧ Wires ks s ∧
      v (ks.getD 0 0) = kw (Dfull 0) ∧ v (ks.getD 1 0) = kw (Dfull 1))
    (fun s ks s' v _ hp he hq => ⟨hp.1.step he hq.2, hq.1.1, hq.1.2.1,
      (hq.1.2.2 0).trans (by rw [hp.2.2]; rfl), (hq.1.2.2 1).trans (by rw [hp.2.2]; rfl)⟩) fun ks => ?_
  refine CGood.seq (k₂ := 1) ((split_cgood (ks.getD 0 0)).stmt.pre fun s v h =>
      ⟨h.2.2.1 _ (getD_mem (by rw [h.2.1]; norm_num)), kw_isK h.2.2.2.1⟩)
    (P₂ := fun lo s v => SigG j p m e pp mlo mhi z bits idx s v ∧ ks.length = 4 ∧ Wires ks s ∧
      v (ks.getD 1 0) = kw (Dfull 1) ∧ BitsOf lo (Dfull 0).toNat s v)
    (fun s lo s' v _ hp he hq => ⟨hp.1.step he hq.2, hp.2.1, hp.2.2.1.mono he, hp.2.2.2.2, hq.1.1, hq.1.2.1,
      fun i hi => by rw [hq.1.2.2 i hi, hp.2.2.2.1, toWord_kw]⟩) fun lo => ?_
  refine CGood.seq (k₂ := 1) ((split_cgood (ks.getD 1 0)).stmt.pre fun s v h =>
      ⟨h.2.2.1 _ (getD_mem (by rw [h.2.1]; norm_num)), kw_isK h.2.2.2.1⟩)
    (P₂ := fun hi s v => SigG j p m e pp mlo mhi z bits idx s v ∧ BitsOf lo (Dfull 0).toNat s v ∧
      BitsOf hi (Dfull 1).toNat s v)
    (fun s hi s' v _ hp he hq => ⟨hp.1.step he hq.2, hp.2.2.2.2.mono he, hq.1.1, hq.1.2.1,
      fun i hi' => by rw [hq.1.2.2 i hi', hp.2.2.2.1, toWord_kw]⟩) fun hi => ?_
  have h63a' : (Dfull 0).toNat.testBit 63 = false := h63a
  have h63b' : (Dfull 1).toNat.testBit 63 = false := h63b
  refine CGood.seq (k₂ := 1) ((eqConstK_cgood (lo.getD 63 0) 0).stmt.pre fun s v h =>
      ⟨h.2.1.2.1 _ (getD_mem (by rw [h.2.1.1]; norm_num)),
        by rw [h.2.1.2.2 63 (by norm_num), bitK_eq, h63a', ofWord_zero]; rfl⟩)
    (P₂ := fun _ s v => SigG j p m e pp mlo mhi z bits idx s v ∧ BitsOf lo (Dfull 0).toNat s v ∧
      BitsOf hi (Dfull 1).toNat s v)
    (fun s _ s' v _ hp he hq => ⟨hp.1.step he hq.2, hp.2.1.mono he, hp.2.2.mono he⟩) fun _ => ?_
  refine CGood.seq (k₂ := 1) ((eqConstK_cgood (hi.getD 63 0) 0).stmt.pre fun s v h =>
      ⟨h.2.2.2.1 _ (getD_mem (by rw [h.2.2.1]; norm_num)),
        by rw [h.2.2.2.2 63 (by norm_num), bitK_eq, h63b', ofWord_zero]; rfl⟩)
    (P₂ := fun _ s v => SigG j p m e pp mlo mhi z bits idx s v ∧ BitsOf lo (Dfull 0).toNat s v ∧
      BitsOf hi (Dfull 1).toNat s v)
    (fun s _ s' v _ hp he hq => ⟨hp.1.step he hq.2, hp.2.1.mono he, hp.2.2.mono he⟩) fun _ => ?_
  try dsimp only
  refine CGood.seq (k₂ := 1) ((digitProduct_cg (List.take 63 lo ++ List.take 63 hi) (bitsB Dfull)).stmt.pre
      fun s v h => dbits_of lo hi Dfull s v h.2.1 h.2.2)
    (P₂ := fun prod s v => SigG j p m e pp mlo mhi z bits idx s v ∧
      DBits (List.take 63 lo ++ List.take 63 hi) (bitsB Dfull) s v ∧ prod < s.next ∧
      v prod = eVal (emb (root ^ psum (bitsB Dfull) 42)))
    (fun s prod s' v _ hp he hq => ⟨hp.1.step he hq.2, dbits_of lo hi Dfull s' v (hp.2.1.mono he)
      (hp.2.2.mono he), hq.1⟩) fun prod => ?_
  refine CGood.seq (k₂ := 1) ((eqConstE_cgood prod Circuit.targetWord 0 0).stmt.pre fun s v h =>
      ⟨h.2.2.1, by rw [h.2.2.2, psum_eq, hsum, ofWord_zero, toE_emb, target_eq]⟩)
    (P₂ := fun _ s v => SigG j p m e pp mlo mhi z bits idx s v ∧
      DBits (List.take 63 lo ++ List.take 63 hi) (bitsB Dfull) s v)
    (fun s _ s' v _ hp he hq => ⟨hp.1.step he hq.2, hp.2.1.mono he⟩) fun _ => ?_
  try dsimp only
  refine (CGood.seq (k₂ := 1) ((forIn_cgood 0 _ (List.range 42)
      (fun i ends s v => SigG j p m e pp mlo mhi z bits idx s v ∧ DBits (List.take 63 lo ++ List.take 63 hi) (bitsB Dfull) s v ∧ LW ends (endsW e p sig x i) s v) ?_ []).pre
      fun s v h => ⟨h.1, h.2, by simp [endsW], wires_nil, fun i hi => absurd hi (by simp)⟩)
    (P₂ := fun r s v => SigG j p m e pp mlo mhi z bits idx s v ∧ LW r (endsW e p sig x 42) s v)
    (fun s r s' v _ _ _ hq => ⟨hq.1, by simpa using hq.2.2⟩) fun ends => ?_).kEq (by simp)
  · intro i hi42 ends
    simp only [List.length_range] at hi42
    simp only [List.getElem_range]
    try dsimp only
    refine CGood.seq (k₂ := 0) ((wire_cgood (limbs3 (tipN sig i).1 (tipN sig i).2 0)).stmt.pre fun _ _ _ => trivial)
      (P₂ := fun tip s v => (SigG j p m e pp mlo mhi z bits idx s v ∧ DBits (List.take 63 lo ++ List.take 63 hi) (bitsB Dfull) s v ∧ LW ends (endsW e p sig x i) s v) ∧ tip < s.next ∧
        v tip = limbs3 (tipN sig i).1 (tipN sig i).2 0)
      (fun s t s' v _ hp he hq => ⟨⟨hp.1.step he hq.2, hp.2.1.mono he, hp.2.2.mono he⟩,
        by rw [hq.1.2.1, hq.1.1]; exact Nat.lt_succ_self _, hq.1.2.2⟩) fun tip => ?_
    refine CGood.seq (k₂ := 0) ((indicators_cg ((List.take 63 lo ++ List.take 63 hi).getD (3 * i) 0)
        ((List.take 63 lo ++ List.take 63 hi).getD (3 * i + 1) 0)
        ((List.take 63 lo ++ List.take 63 hi).getD (3 * i + 2) 0)
        (fun k => bitsB Dfull (3 * i + k))).stmt.pre fun s v h => ?_)
      (P₂ := fun ind s v => ((SigG j p m e pp mlo mhi z bits idx s v ∧ DBits (List.take 63 lo ++ List.take 63 hi) (bitsB Dfull) s v ∧ LW ends (endsW e p sig x i) s v) ∧ tip < s.next ∧
        v tip = limbs3 (tipN sig i).1 (tipN sig i).2 0) ∧
        IndList ind 8 (bdig (fun k => bitsB Dfull (3 * i + k)) 3) s v)
      (fun s ind s' v _ hp he hq => ⟨⟨⟨hp.1.1.step he hq.2, hp.1.2.1.mono he, hp.1.2.2.mono he⟩,
        lt_of_lt_of_le hp.2.1 he.next, hp.2.2⟩, hq.1⟩) fun ind => ?_
    · obtain ⟨⟨-, ⟨hdbl, hdbw, hdbv⟩, -⟩, -, -⟩ := h
      refine ⟨rfl, wires3 (hdbw _ (getD_mem (by rw [hdbl]; omega))) (hdbw _ (getD_mem (by rw [hdbl]; omega)))
        (hdbw _ (getD_mem (by rw [hdbl]; omega))), fun k hk => ?_⟩
      interval_cases k
      · exact hdbv _ (by omega)
      · exact hdbv _ (by omega)
      · exact hdbv _ (by omega)
    have hxi : bdig (fun k => bitsB Dfull (3 * i + k)) 3 = x.getD i 0 := by
      rw [hx, digits_getD Dfull i hi42, bdig_three, dig_three]
      simp only [Nat.add_zero]
    refine CGood.seq (k₂ := 0) ((CGood.hyp fun hpl => chainEnd_cg i idx tip pp ind e p (tipN sig i)
        (bdig (fun k => bitsB Dfull (3 * i + k)) 3) hi42 (bdig_lt _ 3) hpl).stmt.pre fun s v h =>
          ⟨h.1.1.1.2.1.1, h.1.1.1.2.2.2.2.2.2.2.1, h.1.1.1.2.2.2.2.2.2.2.2, h.1.1.1.2.1.ppw, h.1.2.1, h.1.2.2,
            h.2⟩)
      (P₂ := fun a s v => (SigG j p m e pp mlo mhi z bits idx s v ∧ DBits (List.take 63 lo ++ List.take 63 hi) (bitsB Dfull) s v ∧ LW ends (endsW e p sig x i) s v) ∧ a.1 < s.next ∧ a.2 < s.next ∧
        v a.1 = kw (endN e p sig x i).1 ∧ v a.2 = kw (endN e p sig x i).2)
      (fun s a s' v _ hp he hq => ⟨⟨hp.1.1.1.step he hq.2, hp.1.1.2.1.mono he, hp.1.1.2.2.mono he⟩, hq.1.1,
        hq.1.2.1, by rw [hq.1.2.2.1, endN, ← hxi], by rw [hq.1.2.2.2, endN, ← hxi]⟩) fun a => ?_
    obtain ⟨n0, n1⟩ := a
    try dsimp only
    exact CGood.pure' fun s v _ h => ⟨_, rfl, h.1.1, h.1.2.1, by
      rw [endsW_succ]; exact h.1.2.2.append (lw2 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)⟩
  try dsimp only
  refine CGood.seq (k₂ := 1) ((CGood.hyp fun hl => tweakHash_cg 2 0 idx pp ends
      (tw_bound 2 0 (by norm_num) (by norm_num)) hl).stmt.pre fun s v h => ⟨by
        rw [h.1.2.1.1, h.2.1, endsW_length]; norm_num,
        hashPre_of h.1.2.2.2.2.2.2.2.1 h.1.2.2.2.2.2.2.2.2 h.1.2.1 h.2⟩)
    (P₂ := fun node s v => SigG j p m e pp mlo mhi z bits idx s v ∧ node < s.next ∧
      ∃ Dn : Fin 4 → Words.W, v node = dVal Dn ∧ (Dn 0, Dn 1) = climbN e p sig L 0)
    (fun s node s' v _ hp he hq => ⟨hp.1.step he hq.2, hq.1.1, _, hq.1.2, by
      rw [th_words _ _ e p idx pp ends v hp.1.2.2.2.2.2.2.2.2 hp.1.2.1.ppw, hp.2.map]
      exact dVal_th _ _ _ _ _⟩) fun node => ?_
  refine (CGood.seq (k₂ := 1) ((forIn_cgood 0 _ (List.range 32)
      (fun l nd s v => SigG j p m e pp mlo mhi z bits idx s v ∧ nd < s.next ∧
        ∃ Dn : Fin 4 → Words.W, v nd = dVal Dn ∧ (Dn 0, Dn 1) = climbN e p sig L l) ?_ node).pre fun s v h => h)
    (P₂ := fun r s v => SigG j p m e pp mlo mhi z bits idx s v ∧ r < s.next ∧ ∃ Dn : Fin 4 → Words.W, v r = dVal Dn ∧ (Dn 0, Dn 1) = rt)
    (fun s r s' v _ _ _ hq => by
      obtain ⟨hg, hr, Dn, h1, h2⟩ := hq
      exact ⟨hg, hr, Dn, h1, h2.trans hroot⟩) fun r => ?_).kEq (by simp)
  · intro l hl nd
    simp only [List.length_range] at hl
    simp only [List.getElem_range]
    try dsimp only
    refine CGood.seq (k₂ := 0) ((indexWord_cg bits (l + 1) e he32 (by omega)).stmt.pre fun s v h => h.1.2.2.2.2.2.2.1)
      (P₂ := fun ix s v => (SigG j p m e pp mlo mhi z bits idx s v ∧ nd < s.next ∧
        ∃ Dn : Fin 4 → Words.W, v nd = dVal Dn ∧ (Dn 0, Dn 1) = climbN e p sig L l) ∧ ix < s.next ∧
        v ix = kw (Words.tweak1 (e / 2 ^ (l + 1))))
      (fun s ix s' v _ hp he hq => ⟨⟨hp.1.step he hq.2, lt_of_lt_of_le hp.2.1 he.next, hp.2.2⟩, hq.1⟩)
      fun ix => ?_
    apply CGood.intro
    intro s₀ val₀
    have hD : ∀ s v, s = s₀ → Agree s.next val₀ v → nd < s.next →
        ∀ Dn : Fin 4 → Words.W, v nd = dVal Dn → words4 (val₀ nd) = Dn := by
      intro s v hs hag hnd Dn hDn
      rw [← hag nd hnd, hDn, words4_dVal]
    refine CGood.seq (k₂ := 0) ((CGood.hyp fun hpl => level_cg l ix (bits.getD l 0) nd pp (e / 2 ^ (l + 1)) p
        (pathN sig l) (e.testBit l) (words4 (val₀ nd)) hl hpl).stmt.pre fun s v h => ?_)
      (P₂ := fun nd' s v => SigG j p m e pp mlo mhi z bits idx s v ∧ nd' < s.next ∧
        ∃ Dn : Fin 4 → Words.W, v nd' = dVal Dn ∧ (Dn 0, Dn 1) = climbN e p sig L (l + 1))
      ?_ fun nd' => ?_
    · obtain ⟨hs, hag, ⟨hg, hnd, Dn, hDn, -⟩, hix, hixv⟩ := h
      have hb := hg.2.2.2.2.2.2.1
      refine ⟨hg.2.1.1, hix, hixv, hg.2.1.ppw, hb.2.1 _ (getD_mem (by rw [hb.1]; omega)),
        by rw [hb.2.2 l (by omega), bitK_eq], hnd, by rw [hD s v hs hag hnd Dn hDn, hDn]⟩
    · rintro s nd' s' v _ ⟨hs, hag, ⟨hg, hnd, Dn, hDn, hcl⟩, -, -⟩ he ⟨⟨hr, hrv⟩, hst⟩
      refine ⟨hg.step he hst, hr, _, hrv, ?_⟩
      rw [climbN_succ, ← hcl, ← hD s v hs hag hnd Dn hDn, Words.parent]
      cases e.testBit l
      · exact dVal_th _ _ _ _ _
      · exact dVal_th _ _ _ _ _
    · exact CGood.pure' fun s v _ h => ⟨nd', rfl, h⟩
  try dsimp only
  refine CGood.seq (k₂ := 1) ((dToK_cgood r).stmt.pre fun s v h => h.2.1)
    (P₂ := fun rs s v => SigG j p m e pp mlo mhi z bits idx s v ∧ rs.length = 4 ∧ Wires rs s ∧ v (rs.getD 0 0) = kw rt.1 ∧
      v (rs.getD 1 0) = kw rt.2)
    (fun s rs s' v _ hp he hq => by
      obtain ⟨hg, -, Dn, hDn, hrt⟩ := hp
      refine ⟨hg.step he hq.2, hq.1.1, hq.1.2.1, (hq.1.2.2 0).trans ?_, (hq.1.2.2 1).trans ?_⟩
      · rw [hDn, ← hrt]; rfl
      · rw [hDn, ← hrt]; rfl) fun rs => ?_
  refine CGood.seq (k₂ := 1) ((kToE_cgood (rs.getD 0 0) (rs.getD 1 0) z).stmt.pre fun s v h =>
      ⟨wires3 (h.2.2.1 _ (getD_mem (by rw [h.2.1]; norm_num))) (h.2.2.1 _ (getD_mem (by rw [h.2.1]; norm_num)))
        h.1.2.2.2.2.1, kw_isK h.2.2.2.1, kw_isK h.2.2.2.2, by rw [h.1.2.2.2.2.2.1]; rfl⟩)
    (P₂ := fun root s v => s.statement = 5 * j + 4 ∧ root < s.next ∧ v root = limbs3 rt.1 rt.2 0)
    (fun s root s' v _ hp he hq => ⟨by rw [hq.2, hp.1.1], hq.1.1, by
      rw [hq.1.2, hp.2.2.2.1, hp.2.2.2.2, hp.1.2.2.2.2.2.1]
      funext k
      fin_cases k <;> simp [kw, kVal, limbs3, ofWord_zero]⟩) fun root => ?_
  refine CGood.seq (k₂ := 0) ((expose_cgood root).pre fun s v h => ⟨h.2.1, by rw [h.2.2, h.1]; exact h4.symm⟩)
    (P₂ := fun _ _ _ => True) (fun _ _ _ _ _ _ _ _ => trivial) fun _ => ?_
  exact CGood.pure' fun _ _ _ _ => trivial

end

/-! The circuit. -/

section

variable {st : ℕ → Fin 4 → K}

theorem circuit_cg (n : ℕ) (h : ∀ j < n, ∃ pp root msg epoch, Encodes st j pp root msg epoch ∧
      ∃ sig, Words.verify pp root msg epoch sig = true) :
    CGood st (5 * n) (fun s _ => s.statement = 0) (Circuit.circuit n) fun _ _ _ _ => True := by
  unfold Circuit.circuit
  refine (CGood.seq (k₂ := 0) ((forIn_cgood 5 _ (List.range n) (fun i _ s _ => s.statement = 5 * i) ?_
      PUnit.unit).pre fun s _ h => by rw [h])
    (P₂ := fun _ _ _ => True) (fun _ _ _ _ _ _ _ _ => trivial) fun _ =>
      CGood.pure' fun _ _ _ _ => trivial).kEq (by simp)
  intro i hi b
  simp only [List.length_range] at hi
  try simp only [List.getElem_range]
  obtain ⟨pp, root, msg, epoch, henc, sig, hv⟩ := h i hi
  exact CGood.seq (k₂ := 0) (signature_cg i pp root msg epoch sig henc hv).stmt
    (P₂ := fun _ s _ => s.statement = 5 * (i + 1)) (fun s _ s' v _ hp _ hq => by rw [hq.2, hp]; ring)
    fun _ => CGood.pure' fun _ _ _ h => ⟨_, rfl, h⟩

end

theorem sat_empty (st : ℕ → Fin 4 → K) (val : Val) : Sat st ({} : State) val :=
  ⟨fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h,
    fun _ h => by simp at h, fun _ h => by simp at h, fun _ _ h => by simp at h⟩

/-- Completeness: when every signature's statement words encode a public parameter, root, message and epoch with a
signature `Words.verify` accepts, an assignment satisfies the circuit verifying `n` signatures. -/
theorem complete (n : ℕ) (st : ℕ → Fin 4 → K)
    (h : ∀ j < n, ∃ pp root msg epoch, Encodes st j pp root msg epoch ∧
      ∃ sig, Words.verify pp root msg epoch sig = true) :
    ∃ val, Sat st ((Circuit.circuit n).run {}).2 val := by
  obtain ⟨-, -, -, -, val', -, hsat, -⟩ :=
    circuit_cg n h {} (fun _ _ => 0) inv_empty closed_empty (sat_empty st _) fun _ _ => rfl
  exact ⟨val', hsat⟩


end LeanVMCircuits.Xmss
