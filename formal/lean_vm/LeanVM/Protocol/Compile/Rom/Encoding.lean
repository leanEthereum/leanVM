/-
  LeanVM.Protocol.Compile.Rom.Encoding

  The encodings of the compiled verifier are injective, the sponge's permutation inputs are read
  back, and the functions of a Keccak state the verifier reads are uniform: the challenge, the
  capacity, and the proof-of-work lane, independent of the challenge.
-/

module

public import Statement.LeanVmVerifier
public import LeanVM.Facts.Verifier
public import Statement.Fast.Keccak
public import Statement.Fast.QuadExt
public import Statement.Fast.FieldWords
public import LeanVM.Protocol.Compile.Prog
public import LeanVM.Protocol.KeccakHash
public import LeanVM.Parameters.Field

/-!
# Encodings and uniformity for the random-oracle theorem

The random-oracle theorem of the compiled verifier (`LeanVM.Protocol.Compile.Rom.Sound`) reads
the oracles' log back into the verifier's operations, and averages over one fresh answer at a
time. Both rest on facts about the encodings of `LeanVM.Protocol.Compile.run`, collected here.

* **Injectivity.** A `K` word is its 8 bytes (`kBytes_injective`), a list of words of a given
  length its bytes (`flatMap_kBytes_inj`), a Merkle node's input its two children
  (`pairInput_inj`). `chunkAt o x` is the 32 bytes at offset `o` of an input: the children of a
  Merkle node sit at offsets `0` and `32`.
* **Permutation inputs.** A permutation of the sponge (`duplex`) hashes `duplexOf c ps`: the
  waiting scalars' lanes, zeros, and the capacity `c`, lanes `16..25` of the state (`capOf`).
  The capacity is read back (`capOf_duplexOf`), and so are the waiting scalars, when there are at
  most four with tags `1` or `4` (`parsePending_duplexOf`, slot by slot `slotE`, `slotTag`).
  The seed's input has the zero capacity and carries the IV in lanes `0..4` (`laneDigest`).
* **Uniformity.** The challenge of a uniform state is uniform on `E` (`sum_challengeOf_div`); the
  capacity of a uniform state takes a given value with probability `2^-576 ≤ 2^-256`
  (`sum_capOf_div_le`); the proof-of-work predicate on the challenge of a uniform state holds
  with probability at most `2^-min(b, 64)` (`sum_powOk_div_le`), and exactly `2^-b` for
  `b ≤ 64` (`sum_powOk_div_eq`).
-/

namespace LeanVM.Protocol.Compile.Rom

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash
open scoped ENNReal

@[expose] public section

/-! ## Indicators -/

open Classical in
/-- The indicator of a predicate, in `ℝ≥0∞`. -/
noncomputable def ind (p : Prop) : ℝ≥0∞ := if p then 1 else 0

theorem ind_le_one (p : Prop) : ind p ≤ 1 := by
  unfold ind; split <;> simp

theorem ind_of {p : Prop} (h : p) : ind p = 1 := by simp [ind, h]

theorem ind_of_not {p : Prop} (h : ¬ p) : ind p = 0 := by simp [ind, h]

theorem ind_mono {p q : Prop} (h : p → q) : ind p ≤ ind q := by
  by_cases hp : p
  · rw [ind_of hp, ind_of (h hp)]
  · rw [ind_of_not hp]; exact bot_le

theorem ind_or_le (p q : Prop) : ind (p ∨ q) ≤ ind p + ind q := by
  by_cases hp : p
  · rw [ind_of (Or.inl hp), ind_of hp]; exact le_self_add
  · by_cases hq : q
    · rw [ind_of (Or.inr hq), ind_of hq]; exact le_add_self
    · rw [ind_of_not (by tauto)]; exact bot_le

/-- A predicate with at most one witness has indicator sum at most one. -/
theorem sum_ind_le_one {γ : Type} [Fintype γ] {p : γ → Prop}
    (h : ∀ u u', p u → p u' → u = u') :
    ∑ u, ind (p u) ≤ 1 := by
  classical
  have : ∑ u, ind (p u) = ((Finset.univ.filter p).card : ℝ≥0∞) := by
    simp only [ind]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [this]
  exact_mod_cast Finset.card_le_one.mpr fun a ha b hb ↦
    h a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2

/-- An average of terms each at most `c` is at most `c`. -/
theorem avg_le_of_le {γ : Type} [Fintype γ] {f : γ → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ u, f u ≤ c) :
    (∑ u, f u) / Fintype.card γ ≤ c := by
  refine ENNReal.div_le_of_le_mul ?_
  calc ∑ u, f u ≤ ∑ _u : γ, c := Finset.sum_le_sum fun u _ ↦ h u
    _ = c * Fintype.card γ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-! ## Lengths and injectivity of the byte encodings -/

/-- A `flatMap` of an injective function with outputs of one length is injective on lists of
one length. -/
theorem flatMap_inj_of_length {α β : Type} {f : α → List β} {n : ℕ}
    (hlen : ∀ a, (f a).length = n) (hf : Function.Injective f) :
    ∀ {l l' : List α}, l.length = l'.length → l.flatMap f = l'.flatMap f → l = l' := by
  intro l
  induction l with
  | nil => intro l' hl _; exact (List.length_eq_zero_iff.mp hl.symm).symm
  | cons a l ih =>
    intro l' hl h
    obtain _ | ⟨a', l'⟩ := l'
    · simp at hl
    simp only [List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by rw [hlen, hlen])
    rw [hf h1, ih (by simpa using hl) h2]

theorem kBytes_injective : Function.Injective K.toBytes := fun _ _ h ↦
  K.lane_injective (wordBytes_injective h)

/-- Two lists of `K` words of one length with the same bytes are equal. -/
theorem flatMap_kBytes_inj {ws ws' : List K} (hl : ws.length = ws'.length)
    (h : ws.flatMap K.toBytes = ws'.flatMap K.toBytes) : ws = ws' :=
  flatMap_inj_of_length kBytes_length kBytes_injective hl h

/-- The input of a Merkle node: two digests. -/
theorem pairInput_inj {a b a' b' : Digest}
    (h : digestBytes a ++ digestBytes b = digestBytes a' ++ digestBytes b') : a = a' ∧ b = b' := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by rw [digestBytes_length, digestBytes_length])
  exact ⟨digestBytes_injective h1, digestBytes_injective h2⟩

/-- The 32 bytes at offset `o` of an input. -/
def chunkAt (o : ℕ) (x : Bytes) : Bytes := (x.drop o).take 32

theorem chunkAt_zero_append (c : Digest) (b : Bytes) :
    chunkAt 0 (digestBytes c ++ b) = digestBytes c := by
  simp [chunkAt, digestBytes_length]

theorem chunkAt_32_append (c c' : Digest) :
    chunkAt 32 (digestBytes c ++ digestBytes c') = digestBytes c' := by
  simp [chunkAt, digestBytes_length]

/-! ## Permutation inputs -/

/-- The capacity of a state: lanes `16..25`, the part a permutation keeps. -/
def capOf (u : KeccakState) : Fin 9 → UInt64 := fun i ↦ Keccak.lane u (16 + i.val)

/-- The input of a permutation from the capacity `c` with the waiting scalars `ps`: their lanes,
zeros up to lane `16`, then the capacity. -/
def duplexOf (c : Fin 9 → UInt64) (ps : List (E × ℕ)) : KeccakState :=
  Vector.ofFn fun i ↦ if h : i.val < 16 then (pendingLanes ps).getD i 0 else c ⟨i.val - 16, by omega⟩

theorem lane_ofFn (f : Fin 25 → UInt64) (i : ℕ) (hi : i < 25) :
    Keccak.lane (Vector.ofFn f) i = f ⟨i, hi⟩ := by
  simp [Keccak.lane, Array.getD, hi]

theorem lane_duplexOf_lt (c : Fin 9 → UInt64) (ps : List (E × ℕ)) {i : ℕ} (hi : i < 16) :
    Keccak.lane (duplexOf c ps) i = (pendingLanes ps).getD i 0 := by
  rw [duplexOf, lane_ofFn _ i (by omega)]
  simp [hi]

@[simp] theorem capOf_duplexOf (c : Fin 9 → UInt64) (ps : List (E × ℕ)) :
    capOf (duplexOf c ps) = c := by
  funext i
  rw [capOf, duplexOf, lane_ofFn _ _ (by omega)]
  simp

/-- A permutation's input is the capacity of the state and the waiting scalars. -/
theorem duplexInput_eq (sp : Sponge) : duplexInput sp = duplexOf (capOf sp.state) sp.pending := by
  ext i hi
  simp only [duplexInput, duplexOf, Vector.getElem_ofFn]
  split
  · rfl
  · simp only [capOf]
    congr 1
    omega

/-- The scalar in slot `i` of a permutation input: lanes `4i, 4i+1`. -/
def slotE (t : KeccakState) (i : ℕ) : E :=
  E.ofLimbs (K.ofLane (Keccak.lane t (4 * i))) (K.ofLane (Keccak.lane t (4 * i + 1)))

/-- The tag in slot `i` of a permutation input: lane `4i + 3`. -/
def slotTag (t : KeccakState) (i : ℕ) : UInt64 := Keccak.lane t (4 * i + 3)

/-- The waiting scalars of a permutation input, read back: the slots up to the first zero tag. -/
def parsePending (t : KeccakState) : List (E × ℕ) :=
  ((List.range 4).takeWhile fun i ↦ slotTag t i ≠ 0).map fun i ↦ (slotE t i, (slotTag t i).toNat)

/-- Waiting scalars as the verifier keeps them: at most four, each tagged `1` or `4`. -/
def ValidPending (ps : List (E × ℕ)) : Prop := ps.length ≤ 4 ∧ ∀ e ∈ ps, e.2 = 1 ∨ e.2 = 4

/-- The four lanes of a waiting scalar: its two limbs, a zero lane, its tag. -/
def scalarLanes : E × ℕ → List UInt64 :=
  fun (x, tag) ↦ [(x.limb 0).lane, (x.limb 1).lane, 0, tag.toUInt64]

theorem pendingLanes_eq (ps : List (E × ℕ)) : pendingLanes ps = ps.flatMap scalarLanes := rfl

/-- The lanes of a list of blocks of four, read at `4i + r`. -/
theorem getD_flatMap_four {α : Type} (g : α → List UInt64) (hg : ∀ a, (g a).length = 4) :
    ∀ (ps : List α) (i r : ℕ), r < 4 →
      (ps.flatMap g).getD (4 * i + r) 0 = if h : i < ps.length then (g ps[i]).getD r 0 else 0
  | [], i, r, _ => by simp
  | a :: ps, 0, r, hr => by
    simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.length_cons,
      Nat.zero_lt_succ, ↓reduceDIte, List.getElem_cons_zero]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hg]; exact hr),
      ← List.getD_eq_getElem?_getD]
  | a :: ps, i + 1, r, hr => by
    simp only [List.flatMap_cons, List.length_cons, Nat.add_lt_add_iff_right,
      List.getElem_cons_succ]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hg]; omega), hg,
      show 4 * (i + 1) + r - 4 = 4 * i + r by omega, ← List.getD_eq_getElem?_getD,
      getD_flatMap_four g hg ps i r hr]

theorem lane_duplexOf_slot (c : Fin 9 → UInt64) (ps : List (E × ℕ)) {i r : ℕ} (hi : i < 4)
    (hr : r < 4) :
    Keccak.lane (duplexOf c ps) (4 * i + r) =
      if h : i < ps.length then (scalarLanes ps[i]).getD r 0 else 0 := by
  rw [lane_duplexOf_lt _ _ (by omega), pendingLanes_eq,
    getD_flatMap_four scalarLanes (fun _ ↦ rfl) ps i r hr]

theorem slotE_duplexOf (c : Fin 9 → UInt64) (ps : List (E × ℕ)) {i : ℕ} (hi : i < ps.length)
    (h4 : i < 4) : slotE (duplexOf c ps) i = ps[i].1 := by
  have h0 := lane_duplexOf_slot c ps h4 (r := 0) (by norm_num)
  have h1 := lane_duplexOf_slot c ps h4 (r := 1) (by norm_num)
  simp only [Nat.add_zero, hi, ↓reduceDIte] at h0 h1
  rw [slotE, h0, h1]
  simp [scalarLanes, ofLimbs_limb]

theorem slotTag_duplexOf (c : Fin 9 → UInt64) (ps : List (E × ℕ)) {i : ℕ} (h4 : i < 4) :
    slotTag (duplexOf c ps) i = if h : i < ps.length then ps[i].2.toUInt64 else 0 := by
  rw [slotTag, lane_duplexOf_slot c ps h4 (r := 3) (by norm_num)]
  split <;> simp [scalarLanes]

/-- **The waiting scalars are read back** from a permutation input, when they are as the
verifier keeps them. -/
theorem parsePending_duplexOf (c : Fin 9 → UInt64) {ps : List (E × ℕ)} (hv : ValidPending ps) :
    parsePending (duplexOf c ps) = ps := by
  obtain ⟨hlen, htag⟩ := hv
  have htw : (List.range 4).takeWhile (fun i ↦ slotTag (duplexOf c ps) i ≠ 0) =
      List.range ps.length := by
    have hne : ∀ i (hi : i < ps.length), slotTag (duplexOf c ps) i ≠ 0 := by
      intro i hi
      rw [slotTag_duplexOf c ps (by omega)]
      simp only [hi, ↓reduceDIte]
      rcases htag ps[i] (List.getElem_mem hi) with h | h <;> rw [h] <;> decide
    have hz : ps.length < 4 → slotTag (duplexOf c ps) ps.length = 0 := by
      intro h
      rw [slotTag_duplexOf c ps h]
      simp
    rcases ps with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨e, _ | ⟨f, rest⟩⟩⟩⟩⟩
    · have z0 : slotTag (duplexOf c []) 0 = 0 := by simpa using hz (by simp)
      simp [List.range_succ, z0]
    · have h0 := hne 0 (by simp)
      have z1 : slotTag (duplexOf c [a]) 1 = 0 := by simpa using hz (by simp)
      simp [List.range_succ, List.takeWhile, h0, z1]
    · have h0 := hne 0 (by simp)
      have h1 := hne 1 (by simp)
      have z2 : slotTag (duplexOf c [a, b]) 2 = 0 := by simpa using hz (by simp)
      simp [List.range_succ, List.takeWhile, h0, h1, z2]
    · have h0 := hne 0 (by simp)
      have h1 := hne 1 (by simp)
      have h2 := hne 2 (by simp)
      have z3 : slotTag (duplexOf c [a, b, d]) 3 = 0 := by simpa using hz (by simp)
      simp [List.range_succ, List.takeWhile, h0, h1, h2, z3]
    · have h0 := hne 0 (by simp)
      have h1 := hne 1 (by simp)
      have h2 := hne 2 (by simp)
      have h3 := hne 3 (by simp)
      simp [List.range_succ, List.takeWhile, h0, h1, h2, h3]
    · simp at hlen; omega
  rw [parsePending, htw]
  refine List.ext_getElem (by simp) fun i h1 h2 ↦ ?_
  simp only [List.getElem_map, List.getElem_range]
  have hi : i < ps.length := by simpa using h1
  rw [slotE_duplexOf c ps hi (by omega), slotTag_duplexOf c ps (by omega)]
  simp only [hi, ↓reduceDIte]
  rcases htag ps[i] (List.getElem_mem hi) with h | h <;> ext <;> simp [h]

/-- The first four lanes of a state, as a digest (the IV of the seed's input). -/
def laneDigest (t : KeccakState) : Digest :=
  #v[Keccak.lane t 0, Keccak.lane t 1, Keccak.lane t 2, Keccak.lane t 3]

theorem laneDigest_seedInput (iv pd : Digest) : laneDigest (seedInput iv pd) = iv := by
  ext i hi
  simp only [laneDigest]
  interval_cases i <;> simp [seedInput, lane_ofFn]

theorem capOf_seedInput (iv pd : Digest) : capOf (seedInput iv pd) = 0 := by
  funext i
  rw [capOf, seedInput, lane_ofFn _ _ (by omega)]
  simp only [show ¬ (16 + (i : ℕ) < 4) by omega, show ¬ (16 + (i : ℕ) < 8) by omega,
    ↓reduceDIte]
  rfl

/-! ## Cardinalities -/

/-- `UInt64` as `Fin (2^64)`. -/
def uint64FinEquiv : UInt64 ≃ Fin (2 ^ 64) where
  toFun w := w.toFin
  invFun i := UInt64.ofFin i
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_uint64 : Fintype.card UInt64 = 2 ^ 64 := by
  rw [Fintype.card_congr uint64FinEquiv, Fintype.card_fin]

theorem card_K : Fintype.card K = 2 ^ 64 := by
  rw [← Fintype.card_congr LeanVM.Protocol.finEquivK, Fintype.card_fin]

/-- A vector of words as a function. -/
def vecEquiv (n : ℕ) : Vector UInt64 n ≃ (Fin n → UInt64) where
  toFun v i := v[i]
  invFun f := Vector.ofFn f
  left_inv _ := Vector.ext fun _ _ ↦ Vector.getElem_ofFn _
  right_inv _ := funext fun _ ↦ Vector.getElem_ofFn _

theorem card_vec (n : ℕ) (inst : Fintype (Vector UInt64 n)) :
    @Fintype.card (Vector UInt64 n) inst = 2 ^ (64 * n) := by
  rw [@Fintype.card_congr _ _ inst _ (vecEquiv n), Fintype.card_fun, Fintype.card_fin,
    card_uint64, ← pow_mul]

/-- `|Digest| = 2^256`. -/
theorem card_digest : Fintype.card Digest = 2 ^ 256 := card_vec 4 _

/-- `|KState| = 2^1600`. -/
theorem card_kstate : Fintype.card KeccakState = 2 ^ 1600 :=
  (card_vec 25 _).trans (by rw [show 64 * 25 = 1600 by norm_num])

/-! ## Averages through an equivalence -/

/-- Averaging a function of the first component of an equivalence is averaging over the first
factor. -/
theorem sum_fst_div {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] [Nonempty γ]
    (e : α ≃ β × γ) (f : β → ℝ≥0∞) :
    (∑ a, f (e a).1) / Fintype.card α = (∑ b, f b) / Fintype.card β := by
  have hs : ∑ a, f (e a).1 = (Fintype.card γ : ℝ≥0∞) * ∑ b, f b := by
    rw [Fintype.sum_equiv e (fun a ↦ f (e a).1) (fun p ↦ f p.1) (fun _ ↦ rfl),
      Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  have hc : (Fintype.card α : ℝ≥0∞) = (Fintype.card γ : ℝ≥0∞) * Fintype.card β := by
    rw [Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul, mul_comm]
  rw [hs, hc, ENNReal.mul_div_mul_left]
  · exact_mod_cast Fintype.card_ne_zero
  · exact ENNReal.natCast_ne_top _

/-- Averaging a function of the second component of an equivalence is averaging over the second
factor. -/
theorem sum_snd_div {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] [Nonempty β]
    (e : α ≃ β × γ) (f : γ → ℝ≥0∞) :
    (∑ a, f (e a).2) / Fintype.card α = (∑ c, f c) / Fintype.card γ :=
  sum_fst_div (e.trans (Equiv.prodComm β γ)) f

/-- A function on `25` lanes as its first `m` lanes and the rest. -/
def splitEquiv (m : ℕ) (hm : m ≤ 25) : KeccakState ≃ (Fin m → UInt64) × (Fin (25 - m) → UInt64) :=
  (vecEquiv 25).trans <|
    (Equiv.arrowCongr (finCongr (by omega : 25 = m + (25 - m))) (Equiv.refl _)).trans <|
      (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl _)).trans (Equiv.sumArrowEquivProdArrow ..)

theorem splitEquiv_fst (m : ℕ) (hm : m ≤ 25) (u : KeccakState) (i : Fin m) :
    (splitEquiv m hm u).1 i = Keccak.lane u i := by
  simp [splitEquiv, vecEquiv, Equiv.sumArrowEquivProdArrow, Keccak.lane, Array.getD,
    show i.val < 25 by omega]

theorem splitEquiv_snd (m : ℕ) (hm : m ≤ 25) (u : KeccakState) (i : Fin (25 - m)) :
    (splitEquiv m hm u).2 i = Keccak.lane u (m + i) := by
  simp [splitEquiv, vecEquiv, Equiv.sumArrowEquivProdArrow, Keccak.lane, Array.getD,
    show m + i.val < 25 by omega]

/-- `E` as two lanes. -/
def lanesEquiv : (Fin 2 → UInt64) ≃ E where
  toFun f := E.ofLimbs (K.ofLane (f 0)) (K.ofLane (f 1))
  invFun x i := (x.limb i).lane
  left_inv f := by funext i; fin_cases i <;> simp
  right_inv x := by simpa using ofLimbs_limb x

/-- A state is its challenge and its other `23` lanes. -/
def challengeEquiv : KeccakState ≃ E × (Fin 23 → UInt64) :=
  (splitEquiv 2 (by norm_num)).trans (Equiv.prodCongr lanesEquiv (Equiv.refl _))

theorem challengeEquiv_fst (u : KeccakState) : (challengeEquiv u).1 = challengeOf u := by
  show lanesEquiv ((splitEquiv 2 (by norm_num)) u).1 = _
  simp only [lanesEquiv, Equiv.coe_fn_mk, splitEquiv_fst]
  rfl

/-- **The challenge of a uniform state is uniform.** -/
theorem sum_challengeOf_div (f : E → ℝ≥0∞) :
    (∑ u : KeccakState, f (challengeOf u)) / Fintype.card KeccakState = (∑ c : E, f c) / Fintype.card E := by
  have := sum_fst_div challengeEquiv f
  simp only [challengeEquiv_fst] at this
  exact this

/-- Three lanes as a challenge (lanes `0, 1`) and a proof of work (lane `2`). -/
def powLanesEquiv : (Fin 3 → UInt64) ≃ E × UInt64 where
  toFun f := (E.ofLimbs (K.ofLane (f 0)) (K.ofLane (f 1)), f 2)
  invFun p := ![(p.1.limb 0).lane, (p.1.limb 1).lane, p.2]
  left_inv f := by funext i; fin_cases i <;> simp
  right_inv p := by
    obtain ⟨x, w⟩ := p
    simpa using ofLimbs_limb x

/-- A state is its challenge, its proof-of-work lane and its other `22` lanes: the permutation
that absorbs a nonce draws the next challenge and the proof of work from disjoint lanes. -/
def powEquiv : KeccakState ≃ (E × UInt64) × (Fin 22 → UInt64) :=
  (splitEquiv 3 (by norm_num)).trans (Equiv.prodCongr powLanesEquiv (Equiv.refl _))

theorem powEquiv_fst (u : KeccakState) :
    (powEquiv u).1 = (challengeOf u, Keccak.lane u 2) := by
  show powLanesEquiv ((splitEquiv 3 (by norm_num)) u).1 = _
  simp only [powLanesEquiv, Equiv.coe_fn_mk, splitEquiv_fst]
  rfl

/-- A state is its rate (`16` lanes) and its capacity. -/
def capEquiv : KeccakState ≃ (Fin 16 → UInt64) × (Fin 9 → UInt64) := splitEquiv 16 (by norm_num)

theorem capEquiv_snd (u : KeccakState) : (capEquiv u).2 = capOf u := by
  funext i
  rw [capEquiv, splitEquiv_snd]
  rfl

/-- **The capacity of a uniform state takes a given value with probability at most `2^-256`**
(exactly `2^-576`). -/
theorem sum_capOf_div_le (c : Fin 9 → UInt64) :
    (∑ u : KeccakState, ind (capOf u = c)) / Fintype.card KeccakState ≤ 2⁻¹ ^ 256 := by
  have h := sum_snd_div capEquiv fun c' ↦ ind (c' = c)
  simp only [capEquiv_snd] at h
  rw [h]
  have h1 : ∑ c' : Fin 9 → UInt64, ind (c' = c) ≤ 1 :=
    sum_ind_le_one fun u u' hu hu' ↦ hu.trans hu'.symm
  have hcard : (Fintype.card (Fin 9 → UInt64) : ℝ≥0∞) = 2 ^ 576 := by
    rw [Fintype.card_fun, Fintype.card_fin, card_uint64, ← pow_mul, Nat.cast_pow, Nat.cast_ofNat]
  calc (∑ c' : Fin 9 → UInt64, ind (c' = c)) / Fintype.card (Fin 9 → UInt64)
      ≤ 1 / 2 ^ 576 := by rw [hcard]; gcongr
    _ ≤ 2⁻¹ ^ 256 := by
      rw [one_div, ← ENNReal.inv_pow]
      exact ENNReal.inv_le_inv.mpr (pow_le_pow_right₀ (by norm_num) (by norm_num))

/-! ## The proof of work -/

/-- At most `2^(64 - min b 64)` 64-bit numbers are divisible by `2^b`. -/
theorem card_filter_mod_pow_eq_zero_le (b : ℕ) :
    (Finset.univ.filter fun i : Fin (2 ^ 64) ↦ i.val % 2 ^ b = 0).card ≤ 2 ^ (64 - min b 64) := by
  set m := min b 64
  have hsub : (Finset.univ.filter fun i : Fin (2 ^ 64) ↦ i.val % 2 ^ b = 0).map
      Fin.valEmbedding ⊆ (Finset.range (2 ^ (64 - m))).image fun j ↦ j * 2 ^ m := by
    intro x hx
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have hdvd : 2 ^ m ∣ i.val :=
      (Nat.pow_dvd_pow 2 (min_le_left b 64)).trans (Nat.dvd_of_mod_eq_zero hi)
    obtain ⟨j, hj⟩ := hdvd
    simp only [Finset.mem_image, Finset.mem_range]
    refine ⟨j, ?_, by rw [hj, mul_comm]⟩
    have hlt := i.isLt
    rw [hj] at hlt
    have h64 : 2 ^ 64 = 2 ^ m * 2 ^ (64 - m) := by
      rw [← pow_add, Nat.add_sub_cancel' (min_le_right b 64)]
    rw [h64] at hlt
    exact Nat.lt_of_mul_lt_mul_left hlt
  calc _ = ((Finset.univ.filter fun i : Fin (2 ^ 64) ↦ i.val % 2 ^ b = 0).map
        Fin.valEmbedding).card := (Finset.card_map _).symm
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_image_le.trans (by rw [Finset.card_range])

/-- Exactly `2^(64 - b)` 64-bit numbers are divisible by `2^b`, for `b ≤ 64`. -/
theorem card_filter_mod_pow_eq_zero {b : ℕ} (hb : b ≤ 64) :
    (Finset.univ.filter fun i : Fin (2 ^ 64) ↦ i.val % 2 ^ b = 0).card = 2 ^ (64 - b) := by
  refine le_antisymm ((card_filter_mod_pow_eq_zero_le b).trans_eq (by rw [min_eq_left hb])) ?_
  have h64 : 2 ^ 64 = 2 ^ (64 - b) * 2 ^ b := by rw [← pow_add, Nat.sub_add_cancel hb]
  let f : Fin (2 ^ (64 - b)) → Fin (2 ^ 64) := fun j ↦ ⟨j.val * 2 ^ b, by
    rw [h64]; exact (Nat.mul_lt_mul_right (Nat.two_pow_pos b)).mpr j.isLt⟩
  have hf : Function.Injective f := fun i j h ↦
    Fin.ext (Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos b) (congrArg Fin.val h))
  calc 2 ^ (64 - b) = (Finset.univ.map ⟨f, hf⟩).card := by simp
    _ ≤ _ := Finset.card_le_card fun x hx ↦ by
        simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk] at hx
        obtain ⟨j, rfl⟩ := hx
        simp [f]

/-- The average over a lane of the proof-of-work predicate, as a count over 64-bit numbers. -/
theorem sum_powOk_lane_div (b : ℕ) :
    (∑ w : UInt64, ind (powOk b w = true)) / Fintype.card UInt64 =
      ((Finset.univ.filter fun i : Fin (2 ^ 64) ↦ i.val % 2 ^ b = 0).card : ℝ≥0∞) /
        ((2 ^ 64 : ℕ) : ℝ≥0∞) := by
  rw [card_uint64]
  refine congrArg (fun z ↦ z / ((2 ^ 64 : ℕ) : ℝ≥0∞)) ?_
  rw [Fintype.sum_equiv uint64FinEquiv (fun w ↦ ind (powOk b w = true))
    (fun i : Fin (2 ^ 64) ↦ if i.val % 2 ^ b = 0 then 1 else 0)
    (fun w ↦ by simp only [ind, powOk, decide_eq_true_eq]; rfl)]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The proof of work on a uniform lane succeeds with probability at most `2^-min(b, 64)`.** -/
theorem sum_powOk_lane_div_le (b : ℕ) :
    (∑ w : UInt64, ind (powOk b w = true)) / Fintype.card UInt64 ≤ 2⁻¹ ^ min b 64 := by
  rw [sum_powOk_lane_div]
  set m := min b 64
  calc (((Finset.univ.filter fun i : Fin (2 ^ 64) ↦ i.val % 2 ^ b = 0).card : ℕ) : ℝ≥0∞)
        / ((2 ^ 64 : ℕ) : ℝ≥0∞)
      ≤ ((2 ^ (64 - m) : ℕ) : ℝ≥0∞) / ((2 ^ 64 : ℕ) : ℝ≥0∞) := by
        gcongr
        exact_mod_cast card_filter_mod_pow_eq_zero_le b
    _ = 2⁻¹ ^ m := by
        have h64 : (2 : ℝ≥0∞) ^ 64 = 2 ^ (64 - m) * 2 ^ m := by
          rw [← pow_add, Nat.sub_add_cancel (min_le_right b 64)]
        rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, h64, ENNReal.div_eq_inv_mul,
          ENNReal.mul_inv (by simp) (by simp), mul_comm (2 ^ (64 - m))⁻¹, mul_assoc,
          ENNReal.inv_mul_cancel (by simp) (by simp), mul_one, ENNReal.inv_pow]

/-- **The proof of work on a uniform lane succeeds with probability exactly `2^-b`**, for
`b ≤ 64`. -/
theorem sum_powOk_lane_div_eq {b : ℕ} (hb : b ≤ 64) :
    (∑ w : UInt64, ind (powOk b w = true)) / Fintype.card UInt64 = 2⁻¹ ^ b := by
  rw [sum_powOk_lane_div, card_filter_mod_pow_eq_zero hb]
  have h64 : (2 : ℝ≥0∞) ^ 64 = 2 ^ (64 - b) * 2 ^ b := by
    rw [← pow_add, Nat.sub_add_cancel hb]
  rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, h64, ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (by simp) (by simp), mul_comm (2 ^ (64 - b))⁻¹, mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one, ENNReal.inv_pow]

/-- **The proof of work and the challenge of a uniform state are independent**: the average of
the proof of work's success on lane `2` times a function of the challenge (lanes `0, 1`) is the
product of the averages. -/
theorem sum_powOk_mul_challengeOf_div (b : ℕ) (f : E → ℝ≥0∞) :
    (∑ u : KeccakState, ind (powOk b (Keccak.lane u 2) = true) * f (challengeOf u)) /
        Fintype.card KeccakState =
      ((∑ w : UInt64, ind (powOk b w = true)) / Fintype.card UInt64) *
        ((∑ c : E, f c) / Fintype.card E) := by
  have h := sum_fst_div powEquiv fun p : E × UInt64 ↦ ind (powOk b p.2 = true) * f p.1
  simp only [powEquiv_fst] at h
  rw [h, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl (by exact_mod_cast Fintype.card_ne_zero))
      (Or.inl (ENNReal.natCast_ne_top _))]
  ring

/-- The proof of work on a uniform state's lane `2`, times a function of its challenge, averages
to at most `2^-min(b, 64)` times the function's average. -/
theorem sum_powOk_mul_challengeOf_div_le (b : ℕ) (f : E → ℝ≥0∞) :
    (∑ u : KeccakState, ind (powOk b (Keccak.lane u 2) = true) * f (challengeOf u)) /
        Fintype.card KeccakState ≤ 2⁻¹ ^ min b 64 * ((∑ c : E, f c) / Fintype.card E) := by
  rw [sum_powOk_mul_challengeOf_div]
  gcongr
  exact sum_powOk_lane_div_le b

/-- **The proof of work on a uniform state succeeds with probability at most
`2^-min(b, 64)`.** -/
theorem sum_powOk_div_le (b : ℕ) :
    (∑ u : KeccakState, ind (powOk b (Keccak.lane u 2) = true)) / Fintype.card KeccakState ≤
      2⁻¹ ^ min b 64 := by
  have h := sum_powOk_mul_challengeOf_div_le b fun _ ↦ 1
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  rwa [ENNReal.div_self (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
    mul_one] at h

/-- **The proof of work on a uniform state succeeds with probability exactly `2^-b`**, for
`b ≤ 64`. -/
theorem sum_powOk_div_eq {b : ℕ} (hb : b ≤ 64) :
    (∑ u : KeccakState, ind (powOk b (Keccak.lane u 2) = true)) / Fintype.card KeccakState =
      2⁻¹ ^ b := by
  have h := sum_powOk_mul_challengeOf_div b fun _ ↦ 1
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  rwa [ENNReal.div_self (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
    mul_one, sum_powOk_lane_div_eq hb] at h

end

end LeanVM.Protocol.Compile.Rom
