module

public import LeanVMCircuits.Rec.Contracts
public import LeanVMCircuits.Rec.Design
public import LeanVMCircuits.Rec.ExtField

@[expose] public section

/-!
A child's kind in rows, for every shape (`Design::kind_bits`).

A node reads a child's kind, its statement's first word, and must read the child's claims on its tier's fixed polynomial at the child's circuit's block. `kindRows sh t kind` is `Design::kind_bits` as a builder program: with two circuits the kind is held to a bit (`square`, `eq_e`); else the product of `kind + code` over the tier's kinds is held to zero, the kind's first limb is split, its bits past the tier's kind bits are held to the tier's (`Shape.above`), its low bits are the `top` bits that select the block, and in the small tier `is_node` is one plus the product of `top_j + 1`.

`kindRows_good`: in every assignment satisfying a circuit containing its rows, the kind is the kind of a circuit `p` of tier `t` (`Shape.code p`, so `Design::position` names it, `position_code`), the `top` bits are the bits of `p`'s index within its tier, and `is_node`, the child's scale, is zero when `p` is the first level and one at every node. This is the binding of a child's kind to its circuit's block of its tier's fixed polynomial, and its scale's value, for every shape `Tree::new` accepts.
-/

namespace LeanVMCircuits.Rec.Model

open LeanVMCircuits.Rec
open LeanVMCircuits.Rec.Design

/-- The product of `kind + code` over the positions `ps`, from `acc`: `Design::kind_bits`'s fold. -/
def vanish (sh : Shape) (kind : ℕ) : List ℕ → ℕ → M ℕ
  | [], acc => pure acc
  | p :: ps, acc => do
    let c ← eConst (sh.code p) 0 0
    let f ← add kind c
    let a ← mul acc f
    vanish sh kind ps a

/-- Hold bit `j` of each wire, from `j`, to bit `j` of `v`: `Design::kind_bits`'s `eq_k_const`s. -/
def holdBits (v : ℕ) : List ℕ → ℕ → M Unit
  | [], _ => pure ()
  | b :: bs, j => do
    eqConstK b (v >>> j % 2)
    holdBits v bs (j + 1)

/-- Each bit as an `E` element: `Design::kind_bits`'s `k_to_e1`s. -/
def tops : List ℕ → M (List ℕ)
  | [] => pure []
  | b :: bs => do
    let y ← kToE1 b
    let ys ← tops bs
    pure (y :: ys)

/-- The product of `t + one` over the `top` bits, from `acc`: `Design::kind_bits`'s `is_first`. -/
def firstFold (o : ℕ) : List ℕ → ℕ → M ℕ
  | [], acc => pure acc
  | t :: ts, acc => do
    let n ← add t o
    let a ← mul acc n
    firstFold o ts a

/-- `Design::kind_bits` for a child of tier `t` whose kind is the wire `kind`: the `top` bits and `is_node`. -/
def kindRows (sh : Shape) (t kind : ℕ) : M (List ℕ × ℕ) := do
  if sh.size = 2 then
    let sq ← square kind
    union sq kind
    pure ([kind], kind)
  else
    let z ← zero
    let o ← one
    let v ← vanish sh kind (List.range' (sh.start t) (sh.stop t - sh.start t)) o
    union v z
    let ks ← eToK kind
    let bits ← split (ks.getD 0 0)
    holdBits (sh.above t) (bits.drop (sh.kindBits t)) 0
    let top ← tops (bits.take (sh.kindBits t))
    if t = 0 then
      let f ← firstFold o top o
      let n ← add f o
      pure (top, n)
    else pure (top, o)

/-! Contracts. -/

/-- Sequencing with the second program run from the first's end state. -/
theorem Good.seq {α β : Type} {P : State → Prop} {m : M α} {f : α → M β} {Q₁ : State → α → State → Prop}
    {Q : State → β → State → Prop} (h₁ : Good P m Q₁)
    (h₂ : ∀ s a s₁, Inv s → P s → Ext s s₁ → Q₁ s a s₁ → Good (· = s₁) (f a) fun _ b s₂ => Q s b s₂) :
    Good P (m >>= f) Q := by
  intro s hs hp
  obtain ⟨hi₁, he₁, hq₁⟩ := h₁ s hs hp
  obtain ⟨hi₂, he₂, hq₂⟩ := h₂ s _ _ hs hp he₁ hq₁ _ hi₁ rfl
  exact ⟨hi₂, he₁.trans he₂, hq₂⟩

theorem ev_code (c : ℕ) : toE (ofWord c) (ofWord 0) (ofWord 0) = emb (ofWord c) := by
  rw [ofWord_zero, toE_emb]

/-- A circuit's own kind in its statement (`Reduced::statement`'s `e_const` of `Design::code`, exposed first): where the exposure holds, the statement word it writes is its wire's value. `checkdesign` checks a circuit's first exposure is at position zero, of a wire whose first maker is the `e_const` of `Shape.code` of its position, or the builder's cached `zero` or `one` when the code is zero or one (`kindConst_ev`). -/
theorem kind_exposed {st : ℕ → Fin 4 → K} {val : Val} {w k c : ℕ} (he : Call.Holds st val [k] (.exposeE w))
    (hc : ev val w = emb (ofWord c)) : toE (st k 0) (st k 1) (st k 2) = emb (ofWord c) := by
  have E : val w = st k := he
  rw [← hc, ev, E]

/-- The value of a kind's constant, from its maker: the `e_const` of the code, or `zero` or `one` for those codes. -/
theorem kindConst_ev {st : ℕ → Fin 4 → K} {val : Val} {w c : ℕ}
    (h : Call.Holds st val [w] (.eConst c 0 0) ∨ (c = 0 ∧ Call.Holds st val [w] .zero) ∨
      (c = 1 ∧ Call.Holds st val [w] .one)) : ev val w = emb (ofWord c) := by
  rcases h with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact (show ev val w = toE (ofWord c) (ofWord 0) (ofWord 0) from h).trans (ev_code c)
  · rw [show ev val w = 0 from h, ofWord_zero, emb_zero]
  · rw [show ev val w = 1 from h, ofWord_one, show emb 1 = 1 from map_one _]

theorem vanish_good (sh : Shape) (kind : ℕ) : ∀ (ps : List ℕ) (acc : ℕ),
    Good (Wires [kind, acc]) (vanish sh kind ps acc) fun _ r s' => r < s'.next ∧ ∀ st val, Sat st s' val →
      ev val r = ev val acc * (ps.map fun p => ev val kind + emb (ofWord (sh.code p))).prod
  | [], acc => Good.pure' fun _ _ hw => ⟨hw acc (by simp), fun _ _ _ => by simp⟩
  | p :: ps, acc => by
    refine Good.seq ((eConst_good (sh.code p) 0 0).pre fun _ _ => trivial) fun s c s1 _ hw he1 ⟨hc, hcv⟩ => ?_
    have hk1 : kind < s1.next := lt_of_lt_of_le (hw kind (by simp)) he1.next
    have ha1 : acc < s1.next := lt_of_lt_of_le (hw acc (by simp)) he1.next
    refine Good.seq ((add_good kind c).pre fun s' hs' => ?_) fun s' f s2 _ hs' he2 ⟨hf, hfv⟩ => ?_
    · subst hs'
      intro w hw'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with rfl | rfl
      · exact hk1
      · exact hc
    subst hs'
    refine Good.seq ((mul_good acc f).pre fun s' hs' => ?_) fun s' a s3 _ hs' he3 ⟨ha, hav⟩ => ?_
    · subst hs'
      intro w hw'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with rfl | rfl
      · exact lt_of_lt_of_le ha1 he2.next
      · exact hf
    subst hs'
    refine ((vanish_good sh kind ps a).pre fun s' hs' => ?_).weaken (fun _ h => h)
      fun s' r s4 _ hs' he4 ⟨hr, hrv⟩ => ⟨hr, fun st val hsat => ?_⟩
    · subst hs'
      intro w hw'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with rfl | rfl
      · exact lt_of_lt_of_le hk1 (he2.trans he3).next
      · exact ha
    · subst hs'
      have h3 := hsat.mono he4
      have h2 := h3.mono he3
      have h1 := h2.mono he2
      rw [hrv st val hsat, hav st val h3, hfv st val h2, hcv st val h1, ev_code, List.map_cons, List.prod_cons,
        mul_assoc]

theorem holdBits_good (v : ℕ) : ∀ (bs : List ℕ) (j : ℕ), Good (fun _ => True) (holdBits v bs j) fun _ _ _ => True
  | [], _ => Good.pure' fun _ _ _ => trivial
  | b :: bs, j => Good.seq ((eqConstK_good b _).pre fun _ _ => trivial) fun _ _ _ _ _ _ _ =>
      ((holdBits_good v bs (j + 1)).pre fun _ _ => trivial)

theorem tops_good : ∀ bs : List ℕ, Good (Wires bs) (tops bs) fun _ r s' => r.length = bs.length ∧ Wires r s' ∧
    ∀ st val, Sat st s' val → ∀ j < bs.length, ev val (r.getD j 0) = emb (val (bs.getD j 0) 0)
  | [] => Good.pure' fun _ _ _ => ⟨rfl, fun _ h => absurd h (by simp), fun _ _ _ j hj => absurd hj (by simp)⟩
  | b :: bs => by
    refine Good.seq ((kToE1_good b).pre fun s hw w hw' => hw w (by simp at hw'; simp [hw']))
      fun s y s1 _ hw he1 ⟨hy, hyv⟩ => ?_
    refine Good.seq ((tops_good bs).pre fun s' hs' => ?_) fun s' ys s2 _ hs' he2 ⟨hl, hws, hysv⟩ => ?_
    · subst hs'
      exact fun w hw' => lt_of_lt_of_le (hw w (List.mem_cons_of_mem _ hw')) he1.next
    subst hs'
    refine Good.pure' fun s3 _ hs3 => ?_
    subst hs3
    refine ⟨by simp [hl], fun w hw' => ?_, fun st val hsat j hj => ?_⟩
    · rcases List.mem_cons.mp hw' with rfl | hw'
      · exact lt_of_lt_of_le hy he2.next
      · exact hws w hw'
    · rcases j with _ | j
      · simpa using hyv st val (hsat.mono he2)
      · simpa using hysv st val hsat j (by simpa using hj)

theorem firstFold_good (o : ℕ) : ∀ (ts : List ℕ) (acc : ℕ),
    Good (Wires (o :: acc :: ts)) (firstFold o ts acc) fun _ r s' => r < s'.next ∧ ∀ st val, Sat st s' val →
      ev val r = ev val acc * (ts.map fun t => ev val t + ev val o).prod
  | [], acc => Good.pure' fun _ _ hw => ⟨hw acc (by simp), fun _ _ _ => by simp⟩
  | t :: ts, acc => by
    refine Good.seq ((add_good t o).pre fun s hw w hw' => hw w (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw' ⊢; tauto))
      fun s n s1 _ hw he1 ⟨hn, hnv⟩ => ?_
    have hw1 : Wires (o :: acc :: t :: ts) s1 := hw.mono he1
    refine Good.seq ((mul_good acc n).pre fun s' hs' => ?_) fun s' a s2 _ hs' he2 ⟨ha, hav⟩ => ?_
    · subst hs'
      intro w hw'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with rfl | rfl
      · exact hw1 w (by simp)
      · exact hn
    subst hs'
    refine ((firstFold_good o ts a).pre fun s' hs' => ?_).weaken (fun _ h => h)
      fun s' r s3 _ hs' he3 ⟨hr, hrv⟩ => ⟨hr, fun st val hsat => ?_⟩
    · subst hs'
      intro w hw'
      simp only [List.mem_cons] at hw'
      rcases hw' with rfl | rfl | hw'
      · exact lt_of_lt_of_le (hw1 w (by simp)) he2.next
      · exact ha
      · exact lt_of_lt_of_le (hw1 w (by simp [hw'])) he2.next
    · subst hs'
      have h2 := hsat.mono he3
      have h1 := h2.mono he2
      rw [hrv st val hsat, hav st val h2, hnv st val h1, List.map_cons, List.prod_cons, mul_assoc]

/-! The values. -/

theorem add_self_E (b : E) : b + b = 0 := by rw [← two_mul, two_E, zero_mul]

theorem eq_of_add_eq_zero_E {a b : E} (h : a + b = 0) : a = b := by
  calc a = a + (b + b) := by rw [add_self_E, add_zero]
    _ = (a + b) + b := by rw [add_assoc]
    _ = b := by rw [h, zero_add]

/-- The vanishing product is zero only at a kind of the tier. -/
theorem vanish_root (sh : Shape) (h : sh.Accepted) (t : ℕ) (ht : t < sh.nTiers) (k : E)
    (hv : ((List.range' (sh.start t) (sh.stop t - sh.start t)).map fun p => k + emb (ofWord (sh.code p))).prod = 0) :
    ∃ p < sh.size, (sh.placeAt p).tier = t ∧ k = emb (ofWord (sh.code p)) := by
  obtain ⟨x, hx, hx0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp hv)
  rw [List.mem_range'_1] at hx
  have hstop : sh.stop t ≤ sh.size := by
    have := nTiers_le sh
    unfold Shape.stop Shape.smallEnd Shape.size
    unfold Shape.nTiers at ht
    rcases sh with ⟨a0, a, _ | ⟨large, _ | s⟩⟩ <;> simp only at ht ⊢ <;> split_ifs <;> omega
  have hp : x < sh.size := by omega
  exact ⟨x, hp, (tier_iff sh h x hp t).mpr ⟨ht, by omega, by omega⟩, eq_of_add_eq_zero_E hx0⟩

/-- A word's split bits, as `E` elements, are its bits. -/
theorem split_bits (c : ℕ) (hc : c < 2 ^ 64) (b : ℕ → K) (hb : ∀ i < 64, b i = 0 ∨ b i = 1)
    (hw : toWord (ofWord c) = num (fun i => if b i = 1 then 1 else 0) 64) (j : ℕ) (hj : j < 64) :
    emb (b j) = if c.testBit j then 1 else 0 := by
  rw [toWord_ofWord c hc] at hw
  have := testBit_num (fun i => if b i = 1 then 1 else 0) 64 j hj
  rw [← hw] at this
  rcases hb j hj with h0 | h1
  · rw [h0] at this ⊢
    simp only [zero_ne_one, if_false] at this
    rw [this]
    simp [emb_zero]
  · rw [h1] at this ⊢
    simp only [if_true] at this
    rw [this]
    simp [emb]

/-- `is_node`: one plus the product of `top_j + 1` is zero exactly when the index is. -/
theorem first_core (idx : ℕ) (vs : List E) (hidx : idx < 2 ^ vs.length)
    (hv : ∀ j (hj : j < vs.length), vs[j] = if idx.testBit j then 1 else 0) :
    (vs.map (· + 1)).prod + 1 = 0 ↔ idx = 0 := by
  constructor
  · intro hz
    by_contra hne
    have hex : ∃ j < vs.length, idx.testBit j = true := by
      by_contra hn
      push Not at hn
      apply hne
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.zero_testBit]
      by_cases hi : i < vs.length
      · simpa using hn i hi
      · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hidx (Nat.pow_le_pow_right (by norm_num) (by omega)))
    obtain ⟨j, hj, hb⟩ := hex
    have h0 : (vs.map (· + 1)).prod = 0 := by
      apply List.prod_eq_zero
      rw [List.mem_map]
      exact ⟨vs[j], List.getElem_mem hj, by rw [hv j hj, if_pos hb, add_self_E]⟩
    rw [h0, zero_add] at hz
    exact one_ne_zero hz
  · rintro rfl
    have : vs.map (· + 1) = vs.map fun _ => (1 : E) := by
      apply List.map_congr_left
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      rw [hv j hj]
      simp
    rw [this, List.map_const', List.prod_replicate, one_pow]
    exact add_self_E 1

/-- A product of zeros and ones is zero or one. -/
theorem prod_zero_or_one : ∀ l : List E, (∀ x ∈ l, x = 0 ∨ x = 1) → l.prod = 0 ∨ l.prod = 1
  | [], _ => Or.inr List.prod_nil
  | x :: l, h => by
    rw [List.prod_cons]
    rcases h x List.mem_cons_self with rfl | rfl
    · exact Or.inl (zero_mul _)
    · rw [one_mul]
      exact prod_zero_or_one l fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- `Design::kind_bits`'s contract. In every assignment satisfying a circuit containing its rows, the child's kind is the kind of a circuit `p` of tier `t`, its `top` bits are the bits of `p`'s index within the tier, and `is_node` (the child's scale) is zero when `p` is the first level and one at every node. -/
theorem kindRows_good (sh : Shape) (h : sh.Accepted) (hs : sh.size < 2 ^ 62) (t : ℕ) (ht : t < sh.nTiers)
    (kind : ℕ) :
    Good (Wires [kind]) (kindRows sh t kind) fun _ r s' => r.2 < s'.next ∧ Wires r.1 s' ∧
      r.1.length = sh.kindBits t ∧ ∀ st val, Sat st s' val → ∃ p < sh.size, (sh.placeAt p).tier = t ∧
        ev val kind = emb (ofWord (sh.code p)) ∧
        (∀ j < sh.kindBits t, ev val (r.1.getD j 0) = if (p - sh.start t).testBit j then 1 else 0) ∧
        ev val r.2 = if p = 0 then 0 else 1 := by
  have hkb := (shift_le sh h hs).1 t ht
  unfold kindRows
  by_cases h2 : sh.size = 2
  · -- Two circuits: the kind is a bit.
    rw [if_pos h2]
    have hn1 : sh.nTiers = 1 := by
      rcases nTiers_eq sh with h1 | h1
      · exact h1
      · exfalso
        obtain ⟨a0, a, cl⟩ := sh
        rcases cl with _ | ⟨large, _ | s⟩ <;> simp [Shape.nTiers] at h1
        have := (h.small large s rfl).1
        simp [Shape.size] at h2
        omega
    obtain rfl : t = 0 := by omega
    have hkb1 : sh.kindBits 0 = 1 := by
      have : sh.stop 0 - sh.start 0 = 2 := by
        unfold Shape.stop Shape.start Shape.smallEnd
        unfold Shape.nTiers at hn1
        rcases sh with ⟨a0, a, _ | ⟨large, _ | s⟩⟩ <;> simp_all
      unfold Shape.kindBits
      rw [this]
      simpa using Nat.clog_pow 2 1 (by norm_num)
    refine Good.seq ((square_good kind).pre fun _ h => h) fun s sq s1 _ hw he1 ⟨hsq, hsqv⟩ => ?_
    refine Good.seq ((union_good sq kind).pre fun _ _ => trivial) fun s' _ s2 _ hs' he2 hu => ?_
    subst hs'
    refine Good.pure' fun s3 _ hs3 => ?_
    subst hs3
    have hk2 : kind < s3.next := lt_of_lt_of_le (hw kind (by simp)) (he1.trans he2).next
    refine ⟨hk2, fun w hw' => by simp at hw'; rw [hw']; exact hk2, by rw [hkb1]; rfl, fun st val hsat => ?_⟩
    have hsqk : ev val sq = ev val kind := by simp only [ev, hsat.unions _ hu]
    have hkk : ev val kind * (ev val kind - 1) = 0 := by
      rw [mul_sub, mul_one, ← hsqv st val (hsat.mono he2), hsqk, sub_self]
    have h0 : (0 : ℕ) < sh.size := by omega
    have h1 : (1 : ℕ) < sh.size := by omega
    have hc0 : sh.code 0 = 0 := ((code_eq_zero sh h 0 h0).1).mpr rfl
    have ht1 : (sh.placeAt 1).tier = 0 := by
      have := tier_lt sh h 1 h1; omega
    have hc1 : sh.code 1 = 1 := by
      rw [code_eq sh h 1 h1, ht1]
      simp [Shape.start]
    rcases mul_eq_zero.mp hkk with hk | hk
    · refine ⟨0, h0, by simp [Shape.placeAt], by rw [hk, hc0, ofWord_zero, emb_zero], fun j hj => ?_, by
        simp [hk]⟩
      obtain rfl : j = 0 := by omega
      simp [hk, Shape.start]
    · have hk' : ev val kind = 1 := sub_eq_zero.mp hk
      refine ⟨1, h1, ht1, by rw [hk', hc1, ofWord_one]; exact (map_one _).symm, fun j hj => ?_, by
        simp [hk']⟩
      obtain rfl : j = 0 := by omega
      simp [hk', Shape.start]
  · -- The vanishing product over the tier's kinds, the kind's bits, `is_node`.
    rw [if_neg h2]
    refine Good.seq (zero_good.pre fun _ _ => trivial) fun s z s1 _ hw he1 ⟨hz, hzv⟩ => ?_
    refine Good.seq (one_good.pre fun _ _ => trivial) fun s' o s2 _ hs' he2 ⟨ho, hov⟩ => ?_
    subst hs'
    have hk2 : kind < s2.next := lt_of_lt_of_le (hw kind (by simp)) (he1.trans he2).next
    refine Good.seq ((vanish_good sh kind _ o).pre fun s' hs' => ?_) fun s' v s3 _ hs' he3 ⟨hv, hvv⟩ => ?_
    · subst hs'
      intro w hw'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with rfl | rfl
      · exact hk2
      · exact ho
    subst hs'
    refine Good.seq ((union_good v z).pre fun _ _ => trivial) fun s' _ s4 _ hs' he4 hu => ?_
    subst hs'
    refine Good.seq ((eToK_good kind).pre fun s' hs' => ?_) fun s' ks s5 _ hs' he5 ⟨hks, hksv⟩ => ?_
    · subst hs'
      intro w hw'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      rw [hw']
      exact lt_of_lt_of_le hk2 (he3.trans he4).next
    subst hs'
    refine Good.seq ((split_good _).pre fun _ _ => trivial) fun s' bits s6 _ hs' he6 ⟨hbl, hbw, hbv⟩ => ?_
    subst hs'
    refine Good.seq ((holdBits_good _ _ 0).pre fun _ _ => trivial) fun s' _ s7 _ hs' he7 _ => ?_
    subst hs'
    refine Good.seq ((tops_good _).pre fun s' hs' => ?_) fun s' top s8 _ hs' he8 ⟨htl, htw, htv⟩ => ?_
    · subst hs'
      exact fun w hw' => lt_of_lt_of_le (hbw w (List.mem_of_mem_take hw')) he7.next
    subst hs'
    have hlen : top.length = sh.kindBits t := by
      rw [htl, List.length_take, hbl]; omega
    -- The semantics shared by both tiers' endings.
    have core : ∀ st val, Sat st s8 val → ∃ p < sh.size, (sh.placeAt p).tier = t ∧
        ev val kind = emb (ofWord (sh.code p)) ∧
        ∀ j < sh.kindBits t, ev val (top.getD j 0) = if (p - sh.start t).testBit j then 1 else 0 := by
      intro st val hsat
      have h7 := hsat.mono he8
      have h6 := h7.mono he7
      have h5 := h6.mono he6
      have h4 := h5.mono he5
      have h3 := h4.mono he4
      have h2' := h3.mono he3
      have hvan : ((List.range' (sh.start t) (sh.stop t - sh.start t)).map
          fun p => ev val kind + emb (ofWord (sh.code p))).prod = 0 := by
        have := hvv st val h3
        rw [hov st val h2', one_mul] at this
        rw [← this]
        have hvz : val v = val z := h4.unions _ hu
        rw [show ev val v = ev val z by simp only [ev, hvz]]
        exact hzv st val (h2'.mono he2)
      obtain ⟨p, hp, hpt, hkp⟩ := vanish_root sh h t ht _ hvan
      refine ⟨p, hp, hpt, hkp, fun j hj => ?_⟩
      have hc := code_lt sh h p hp hs
      -- The kind's first limb is the code's word.
      have hk0 : val kind 0 = ofWord (sh.code p) := by
        have e : toE (val kind 0) (val kind 1) (val kind 2) = toE (ofWord (sh.code p)) 0 0 := by
          rw [toE_emb]; exact hkp
        exact (toE_injective _ _ _ _ _ _ e).1
      have hword : val (ks.getD 0 0) 0 = ofWord (sh.code p) := by
        have e := hksv st val h5 0 (by decide)
        rw [Fin.val_zero] at e
        rw [e]; exact hk0
      obtain ⟨hb01, hbnum⟩ := hbv st val h6
      rw [hword] at hbnum
      have hj64 : j < 64 := by omega
      rw [htv st val hsat j (by rw [List.length_take, hbl]; omega)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hj, ← List.getD_eq_getElem?_getD]
      rw [split_bits _ hc (fun i => val (bits.getD i 0) 0) hb01 hbnum j hj64]
      have hmod := code_mod sh h p hp
      rw [hpt] at hmod
      rw [← hmod, Nat.testBit_mod_two_pow]
      simp [hj]
    split_ifs with ht0
    · subst ht0
      refine Good.seq ((firstFold_good o top o).pre fun s' hs' => ?_) fun s' f s9 _ hs' he9 ⟨hf, hfv⟩ => ?_
      · subst hs'
        intro w hw'
        simp only [List.mem_cons] at hw'
        rcases hw' with rfl | rfl | hw'
        · exact lt_of_lt_of_le ho (he3.trans he4 |>.trans he5 |>.trans he6 |>.trans he7 |>.trans he8).next
        · exact lt_of_lt_of_le ho (he3.trans he4 |>.trans he5 |>.trans he6 |>.trans he7 |>.trans he8).next
        · exact htw w hw'
      subst hs'
      have ho9 : o < s9.next :=
        lt_of_lt_of_le ho (he3.trans he4 |>.trans he5 |>.trans he6 |>.trans he7 |>.trans he8 |>.trans he9).next
      refine Good.seq ((add_good f o).pre fun s' hs' => ?_) fun s' n s10 _ hs' he10 ⟨hn, hnv⟩ => ?_
      · subst hs'
        intro w hw'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
        rcases hw' with rfl | rfl
        · exact hf
        · exact ho9
      subst hs'
      refine Good.pure' fun s11 _ hs11 => ?_
      subst hs11
      refine ⟨hn, htw.mono (he9.trans he10), hlen, fun st val hsat => ?_⟩
      have h9 := hsat.mono he10
      have h8 := h9.mono he9
      obtain ⟨p, hp, hpt, hkp, htop⟩ := core st val h8
      refine ⟨p, hp, hpt, hkp, htop, ?_⟩
      have hone : ev val o = 1 :=
        hov st val (h8.mono (he3.trans he4 |>.trans he5 |>.trans he6 |>.trans he7 |>.trans he8))
      rw [hnv st val hsat, hfv st val h9, hone, one_mul]
      have hs0 : sh.start 0 = 0 := rfl
      have hidx : p - sh.start 0 < 2 ^ (top.map (ev val)).length := by
        rw [List.length_map, hlen]
        have := index_lt sh h p hp
        rwa [hpt] at this
      have e := first_core (p - sh.start 0) (top.map (ev val)) hidx (fun j hj => by
        rw [List.getElem_map]
        have := htop j (by rw [List.length_map] at hj; omega)
        rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hj), Option.getD_some] at this)
      rw [List.map_map] at e
      have e' : (top.map fun x => ev val x + 1).prod + 1 = 0 ↔ p - sh.start 0 = 0 := e
      have h01 : ∀ x ∈ top.map (fun x => ev val x + 1), x = 0 ∨ x = 1 := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
        have hb := htop j (by omega)
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at hb
        rw [hb]
        split_ifs
        · exact Or.inl (add_self_E 1)
        · exact Or.inr (zero_add 1)
      split_ifs with hp0
      · exact e'.mpr (by rw [hs0]; omega)
      · rcases prod_zero_or_one _ h01 with hP | hP
        · rw [hP, zero_add]
        · exfalso
          have := e'.mp (by rw [hP]; exact add_self_E 1)
          rw [hs0] at this
          omega
    · refine Good.pure' fun s9 _ hs9 => ?_
      subst hs9
      refine ⟨lt_of_lt_of_le ho (he3.trans he4 |>.trans he5 |>.trans he6 |>.trans he7 |>.trans he8).next, htw,
        hlen, fun st val hsat => ?_⟩
      obtain ⟨p, hp, hpt, hkp, htop⟩ := core st val hsat
      refine ⟨p, hp, hpt, hkp, htop, ?_⟩
      have hone : ev val o = 1 :=
        hov st val (hsat.mono (he3.trans he4 |>.trans he5 |>.trans he6 |>.trans he7 |>.trans he8))
      rw [hone, if_neg]
      rintro rfl
      have : (sh.placeAt 0).tier = 0 := by simp [Shape.placeAt]
      omega

/-! A node circuit, its transcribed rows abstract. -/

/-- What a child's kind rows bind in an assignment, for the child `x = (kind, top, is_node)` of tier `ct`: its kind is the kind of a circuit `q` of tier `ct`, its `top` bits are `q`'s index's, and `is_node` is zero at the first level and one at every node. -/
def KindBound (sh : Shape) (ct : ℕ) (val : Val) (x : ℕ × List ℕ × ℕ) : Prop :=
  ∃ q < sh.size, (sh.placeAt q).tier = ct ∧ ev val x.1 = emb (ofWord (sh.code q)) ∧
    (∀ j < sh.kindBits ct, ev val (x.2.1.getD j 0) = if (q - sh.start ct).testBit j then 1 else 0) ∧
    ev val x.2.2 = if q = 0 then 0 else 1

/-- `Design::node`'s limbs of a child's words: `k_const 0`, then each word's `e_to_k`. Word `i`'s limbs are its `e_to_k`'s three outputs and the zero (`[c0, c1, c2, zero]`), the statement `RecShape::verify` absorbs and reads (`Edges.InstCert`). -/
def limbRows (ws : List ℕ) : M (ℕ × List (List ℕ)) := do
  let z ← kConst 0
  let ls ← ws.mapM eToK
  pure (z, ls)

/-- What `limbRows` binds in an assignment: the zero is zero, and word `i`'s three limbs are its first three. -/
def LimbsBound (ws : List ℕ) (val : Val) (l : ℕ × List (List ℕ)) : Prop :=
  val l.1 = limbsOf [0, 0, 0, 0] ∧ l.2.length = ws.length ∧
    ∀ i < ws.length, ∀ c : Fin 4, c.val < 3 → val ((l.2.getD i []).getD c 0) 0 = val (ws.getD i 0) c

theorem mapM_eToK_good : ∀ ws : List ℕ, Good (Wires ws) (ws.mapM eToK) fun _ ls s' => ls.length = ws.length ∧
    ∀ st val, Sat st s' val → ∀ i < ws.length, ∀ c : Fin 4, c.val < 3 →
      val ((ls.getD i []).getD c 0) 0 = val (ws.getD i 0) c
  | [] => Good.pure' fun _ _ _ => ⟨rfl, fun _ _ _ i hi => absurd hi (by simp)⟩
  | w :: ws => by
    rw [List.mapM_cons]
    refine Good.seq ((eToK_good w).pre fun s hs x hx => hs x (by simp_all)) fun s ks s1 _ hw he1 hk => ?_
    have hw1 : Wires ws s1 := Wires.mono (fun x hx => hw x (List.mem_cons_of_mem _ hx)) he1
    refine Good.seq ((mapM_eToK_good ws).pre fun s' hs' => hs' ▸ hw1) fun s' ls s2 _ hs' he2 hls => ?_
    subst hs'
    refine Good.pure' fun s3 _ hs3 => ?_
    subst hs3
    refine ⟨by simp [hls.1], fun st val hsat i hi c hc => ?_⟩
    rcases i with _ | i
    · exact hk.2 st val (hsat.mono he2) c hc
    · exact hls.2 st val hsat i (by simpa using hi) c hc

theorem limbRows_good (ws : List ℕ) : Good (Wires ws) (limbRows ws) fun _ l s' => ∀ st val, Sat st s' val →
    LimbsBound ws val l := by
  unfold limbRows
  refine Good.seq ((kConst_good 0).pre fun _ _ => trivial) fun s z s1 _ hw he1 hz => ?_
  refine Good.seq ((mapM_eToK_good ws).pre fun s' hs' => hs' ▸ hw.mono he1) fun s' ls s2 _ hs' he2 hls => ?_
  subst hs'
  refine Good.pure' fun s3 _ hs3 => ?_
  subst hs3
  exact fun st val hsat => ⟨hz.2 st val (hsat.mono he2), hls.1, hls.2 st val hsat⟩

/-- One child as `Design::node` reads it: its statement's `S` words (`free_e`), its kind rows, its words' limbs, then `rest`, the rows that stay transcription (`RecShape::verify` past the statement it absorbs and reads, `bind_state`, the fixed and carried claims, the digest), given the words, the kind rows' outputs and the limbs. It returns the words, the kind rows' outputs and the limbs. -/
def oneChild (sh : Shape) (ct S : ℕ) (rest : List ℕ → List ℕ × ℕ → ℕ × List (List ℕ) → M Unit) :
    M (List ℕ × (List ℕ × ℕ) × (ℕ × List (List ℕ))) := do
  let ws ← (List.range S).mapM fun _ => wire
  let r ← kindRows sh ct (ws.headD 0)
  let l ← limbRows ws
  rest ws r l
  pure (ws, r, l)

/-- What a child's rows bind: its kind (`KindBound`) and its words' limbs (`LimbsBound`). -/
def ChildBound (sh : Shape) (ct : ℕ) (val : Val) (x : List ℕ × (List ℕ × ℕ) × (ℕ × List (List ℕ))) : Prop :=
  KindBound sh ct val (x.1.headD 0, x.2.1) ∧ LimbsBound x.1 val x.2.2

/-- The first `n` children, in order. -/
def readChildren (sh : Shape) (ct S : ℕ) (rest : ℕ → List ℕ → List ℕ × ℕ → ℕ × List (List ℕ) → M Unit) :
    ℕ → M (List (List ℕ × (List ℕ × ℕ) × (ℕ × List (List ℕ))))
  | 0 => pure []
  | n + 1 => do
    let xs ← readChildren sh ct S rest n
    let x ← oneChild sh ct S (rest n)
    pure (xs ++ [x])

/-- `Design::node` at position `p`: its `Shape.children` children of their tier, then `tail`, the rows that stay transcription (the union or the digest, the reduction, the statement's exposure). -/
def nodeRows (sh : Shape) (p S : ℕ) (rest : ℕ → List ℕ → List ℕ × ℕ → ℕ × List (List ℕ) → M Unit) (tail : M Unit) :
    M (List (List ℕ × (List ℕ × ℕ) × (ℕ × List (List ℕ)))) :=
  match sh.children p with
  | some (a, ct) => do
    let xs ← readChildren sh ct S rest a
    tail
    pure xs
  | none => pure []

theorem oneChild_good (sh : Shape) (h : sh.Accepted) (hs : sh.size < 2 ^ 62) (ct : ℕ) (hct : ct < sh.nTiers)
    (S : ℕ) (hS : 1 ≤ S) (rest : List ℕ → List ℕ × ℕ → ℕ × List (List ℕ) → M Unit)
    (hrest : ∀ ws r l, Good (fun _ => True) (rest ws r l) fun _ _ _ => True) :
    Good (fun _ => True) (oneChild sh ct S rest) fun _ x s' => ∀ st val, Sat st s' val → ChildBound sh ct val x := by
  unfold oneChild
  refine Good.seq (mapM_good (fun _ => True) (fun _ _ h _ => h) (fun _ => wire) (fun _ _ => True)
    (fun _ => fresh_good) (List.range S)) fun s ws s1 _ _ he1 ⟨hl, _, hw⟩ => ?_
  have hk : Wires [ws.headD 0] s1 := by
    intro w hw'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    subst hw'
    rcases ws with _ | ⟨w, ws⟩
    · simp at hl; omega
    · exact hw w (by simp)
  refine Good.seq ((kindRows_good sh h hs ct hct _).pre fun s' hs' => hs' ▸ hk) fun s' r s2 _ hs' he2 hr => ?_
  subst hs'
  refine Good.seq ((limbRows_good ws).pre fun s' hs' => hs' ▸ hw.mono he2) fun s' l s3 _ hs' he3 hl3 => ?_
  subst hs'
  refine Good.seq ((hrest ws r l).pre fun _ _ => trivial) fun s' _ s4 _ hs' he4 _ => ?_
  subst hs'
  refine Good.pure' fun s5 _ hs5 => ?_
  subst hs5
  intro st val hsat
  exact ⟨hr.2.2.2 st val ((hsat.mono he4).mono he3), hl3 st val (hsat.mono he4)⟩

theorem readChildren_good (sh : Shape) (h : sh.Accepted) (hs : sh.size < 2 ^ 62) (ct : ℕ) (hct : ct < sh.nTiers)
    (S : ℕ) (hS : 1 ≤ S) (rest : ℕ → List ℕ → List ℕ × ℕ → ℕ × List (List ℕ) → M Unit)
    (hrest : ∀ i ws r l, Good (fun _ => True) (rest i ws r l) fun _ _ _ => True) :
    ∀ n, Good (fun _ => True) (readChildren sh ct S rest n) fun _ xs s' =>
      xs.length = n ∧ ∀ st val, Sat st s' val → ∀ x ∈ xs, ChildBound sh ct val x
  | 0 => Good.pure' fun _ _ _ => ⟨rfl, fun _ _ _ x hx => absurd hx (by simp)⟩
  | n + 1 => by
    refine Good.seq (readChildren_good sh h hs ct hct S hS rest hrest n) fun s xs s1 _ _ he1 ⟨hl, hxs⟩ => ?_
    refine Good.seq ((oneChild_good sh h hs ct hct S hS (rest n) (hrest n)).pre fun _ _ => trivial)
      fun s' x s2 _ hs' he2 hx => ?_
    subst hs'
    refine Good.pure' fun s3 _ hs3 => ?_
    subst hs3
    refine ⟨by simp [hl], fun st val hsat y hy => ?_⟩
    rcases List.mem_append.mp hy with hy | hy
    · exact hxs st val (hsat.mono he2) y hy
    · rw [List.mem_singleton.mp hy]
      exact hx st val hsat

/-- A node circuit, for every accepted shape: whatever its transcribed rows, as long as they keep the builder's invariant (every row a model method's on wires already made, what `checkrec` checks of the tracked dumps), in every assignment satisfying the circuit each of its `Shape.children` children's kind is the kind of a circuit of the child tier, its `top` bits select that circuit's block of the tier's fixed polynomial, `is_node` is zero exactly at the first level, and the limbs its verifier is given are its words' (`ChildBound`). -/
theorem nodeRows_good (sh : Shape) (h : sh.Accepted) (hs : sh.size < 2 ^ 62) (p : ℕ) (hp : p < sh.size)
    (a ct : ℕ) (hc : sh.children p = some (a, ct)) (S : ℕ) (hS : 1 ≤ S)
    (rest : ℕ → List ℕ → List ℕ × ℕ → ℕ × List (List ℕ) → M Unit)
    (hrest : ∀ i ws r l, Good (fun _ => True) (rest i ws r l) fun _ _ _ => True)
    (tail : M Unit) (htail : Good (fun _ => True) tail fun _ _ _ => True) :
    Good (fun _ => True) (nodeRows sh p S rest tail) fun _ xs s' =>
      xs.length = a ∧ ∀ st val, Sat st s' val → ∀ x ∈ xs, ChildBound sh ct val x := by
  have hct := (children_tier sh h p hp a ct hc).1
  unfold nodeRows
  rw [hc]
  refine Good.seq (readChildren_good sh h hs ct hct S hS rest hrest a) fun s xs s1 _ _ he1 ⟨hl, hxs⟩ => ?_
  refine Good.seq (htail.pre fun _ _ => trivial) fun s' _ s2 _ hs' he2 _ => ?_
  subst hs'
  refine Good.pure' fun s3 _ hs3 => ?_
  subst hs3
  exact ⟨hl, fun st val hsat => hxs st val (hsat.mono he2)⟩

end LeanVMCircuits.Rec.Model
