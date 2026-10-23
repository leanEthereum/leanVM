/-
  LeanVM.Guest.B1.Digest.Common

  What the digest, claim-list and LeanDA refinements share: the memory hypothesis, cells read
  through a pointer, straight-line blocks as conjunctions, a chain of compressions as a fold, and
  how a core function is found and unfolded.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.CoreLemmas
public import LeanVM.Guest.Value.All

/-!
# Shared vocabulary of `B1/Digest` and `B1/Da`

* `MemOk rd`: the reader is a memory of `2^κ` words, `16 ≤ κ ≤ 32` (`Spec/Isa.lean`,
  `HasPublicBoundary`), which a range check needs to mean a bound;
* `CellsAt rd p cs`: the words `p·g^k`, `k < cs.length`, hold `cs` (`DEREF`s through `p`);
* `holdsList_atoms`: a run of atoms holds exactly when each does;
* `chainRun`: compressions in sequence under per-block metadata cells, the fold a run of
  `BLAKE2S` instructions computes (`compressCells_chainRun`), and its specification forms
  (`chainRun_nonfinal`, `chainRun_final`);
* `rangeCheck_sound`, `rangeCheck_complete`: the range-check atom against `g^(K-1)` on `MemOk`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-! ## The memory -/

/-- The reader is a memory of `2^κ` words, `16 ≤ κ ≤ 32`, as every valid execution's is. -/
def MemOk (rd : Reader) : Prop := ∃ κ, 16 ≤ κ ∧ κ ≤ 32 ∧ ∃ L : MemImage κ, rd = L.read

/-- A memory word read twice is one word. -/
theorem loadHolds_unique {rd : Reader} {p : E} {k : ℕ} {w w' : E} (h : LoadHolds rd p k w)
    (h' : LoadHolds rd p k w') : w = w' :=
  Option.some.inj (h.2.symm.trans h'.2)

/-- The words `p·g^k`, `k < cs.length`, hold `cs`, `p` in `K` when `cs` is not empty. -/
def CellsAt (rd : Reader) (p : E) (cs : List E) : Prop :=
  ∀ k (h : k < cs.length), LoadHolds rd p k cs[k]

theorem cellsAt_nil (rd : Reader) (p : E) : CellsAt rd p [] := fun _ h => absurd h (by simp)

/-- A word read at offset `0` through a pointer of the memory is a g-power below `2^32`. -/
theorem load_gpow {rd : Reader} (hm : MemOk rd) {x t : E} (h : LoadHolds rd x 0 t) :
    ∃ e < 2 ^ 32, x = gen ^ e := by
  obtain ⟨κ, -, hκ, L, rfl⟩ := hm
  obtain ⟨hx, hr⟩ := h
  rw [Parameters.gpow, pow_zero, mul_one] at hr
  obtain ⟨i, hi, -⟩ := (read_some_iff (by omega) L _ _).mp hr
  refine ⟨i, lt_of_lt_of_le i.2 (Nat.pow_le_pow_right (by decide) hκ), ?_⟩
  rw [eq_ofK_limb hx, hi, gen_pow_eq_ofK]

/-- The memory holds a word at every address `g^e`, `e < 2^16` (range checks read there). -/
def Low16 (rd : Reader) : Prop := ∀ i < 2 ^ 16, (rd (Parameters.gpow i)).isSome

/-- Every address `g^e`, `e < 2^16`, holds a word, on a memory defined there. -/
theorem load_gpow_complete_low {rd : Reader} (hl : Low16 rd) {e : ℕ} (he : e < 2 ^ 16) :
    ∃ t, LoadHolds rd (gen ^ e) 0 t := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hl e he)
  refine ⟨t, ?_, ?_⟩
  · rw [gen_pow_eq_ofK]; exact ofK_isInK _
  · rw [gen_pow_eq_ofK, limb_ofK]
    simp only [Parameters.gpow, pow_zero, mul_one] at ht ⊢
    exact ht

/-- **A range check passes** on a memory defined below `2^16`. -/
theorem rangeCheck_complete_low {rd : Reader} (hl : Low16 rd) {e e' : ℕ} (he : e < 2 ^ 16)
    (he' : e' < 2 ^ 16) :
    ∃ t1 t2, LoadHolds rd (gen ^ e) 0 t1 ∧ gen ^ (e + e') = gen ^ e * gen ^ e' ∧
      LoadHolds rd (gen ^ e') 0 t2 := by
  obtain ⟨t1, h1⟩ := load_gpow_complete_low hl he
  obtain ⟨t2, h2⟩ := load_gpow_complete_low hl he'
  exact ⟨t1, t2, h1, pow_add _ _ _, h2⟩

/-- Every address `g^e`, `e < 2^16`, holds a word. -/
theorem load_gpow_complete {rd : Reader} (hm : MemOk rd) {e : ℕ} (he : e < 2 ^ 16) :
    ∃ t, LoadHolds rd (gen ^ e) 0 t := by
  obtain ⟨κ, hκ, hκ', L, rfl⟩ := hm
  have he' : e < 2 ^ κ := lt_of_lt_of_le he (Nat.pow_le_pow_right (by decide) hκ)
  refine ⟨L ⟨e, he'⟩, ?_, ?_⟩
  · rw [gen_pow_eq_ofK]; exact ofK_isInK _
  · rw [gen_pow_eq_ofK, limb_ofK]
    simp only [Parameters.gpow, pow_zero, mul_one]
    exact (read_some_iff (by omega) L _ _).mpr ⟨⟨e, he'⟩, rfl, rfl⟩

/-- **A range check is sound**: on `MemOk`, its two reads make `x`, `y` g-powers below `2^32`, so
`k = x·y` is `g` to their sum. -/
theorem rangeCheck_sound {rd : Reader} (hm : MemOk rd) {x y t1 t2 k : E}
    (h : LoadHolds rd x 0 t1 ∧ k = x * y ∧ LoadHolds rd y 0 t2) :
    ∃ e e', e < 2 ^ 32 ∧ e' < 2 ^ 32 ∧ x = gen ^ e ∧ y = gen ^ e' ∧ k = gen ^ (e + e') := by
  obtain ⟨e, he, rfl⟩ := load_gpow hm h.1
  obtain ⟨e', he', rfl⟩ := load_gpow hm h.2.2
  exact ⟨e, e', he, he', rfl, rfl, by rw [h.2.1, pow_add]⟩

/-- **A range check is complete** for exponents below `2^16`. -/
theorem rangeCheck_complete {rd : Reader} (hm : MemOk rd) {e e' : ℕ} (he : e < 2 ^ 16)
    (he' : e' < 2 ^ 16) :
    ∃ t1 t2, LoadHolds rd (gen ^ e) 0 t1 ∧ gen ^ (e + e') = gen ^ e * gen ^ e' ∧
      LoadHolds rd (gen ^ e') 0 t2 := by
  obtain ⟨t1, h1⟩ := load_gpow_complete hm he
  obtain ⟨t2, h2⟩ := load_gpow_complete hm he'
  exact ⟨t1, t2, h1, pow_add _ _ _, h2⟩

theorem MemOk.low16 {rd : Reader} (hm : MemOk rd) : Low16 rd := fun i hi => by
  obtain ⟨t, h⟩ := load_gpow_complete hm hi
  have := h.2
  rw [gen_pow_eq_ofK, limb_ofK] at this
  simp only [Parameters.gpow, pow_zero, mul_one] at this ⊢
  simp only [Fin.val_zero, ↓reduceIte] at this
  rw [this]; rfl

/-- A word with zero upper limbs is the integer word. -/
theorem word_eq_eOfNat (c : ℕ) : word c 0 0 = eOfNat c := by
  rw [eOfNat_eq_ofLimbs]; rfl

theorem word_one : word 1 0 0 = 1 := by rw [word_eq_eOfNat, eOfNat_one]

theorem word_gen : word 2 0 0 = gen := word_eq_eOfNat 2

/-- A compile-time non-final counter word is its metadata cell. -/
theorem word_md (c : ℕ) : word c 0 0 = metadataCell c false := rfl

theorem isCanonical128_zero : IsCanonical128 (0 : E) := by
  rw [zero_eq_ofLimbs]; rfl

theorem word_zero : word 0 0 0 = 0 := by rw [word_eq_eOfNat, eOfNat_zero]

/-- `INV_GEN`, the word the guest multiplies a runtime range bound by. -/
theorem ginv_mul_gen : word 9223372036854775821 0 0 * gen = 1 := by
  rw [word_eq_eOfNat, gen, eOfNat, eOfNat, ← ofK_mul, ← ofK_one]
  congr 1

theorem cellsAt_four {rd : Reader} {p r0 r1 r2 r3 : E} :
    CellsAt rd p [r0, r1, r2, r3] ↔ LoadHolds rd p 0 r0 ∧ LoadHolds rd p 1 r1 ∧
      LoadHolds rd p 2 r2 ∧ LoadHolds rd p 3 r3 := by
  constructor
  · intro h
    exact ⟨h 0 (by simp), h 1 (by simp), h 2 (by simp), h 3 (by simp)⟩
  · rintro ⟨h0, h1, h2, h3⟩ k hk
    simp only [List.length_cons, List.length_nil] at hk
    rcases k with _ | _ | _ | _ | k
    exacts [h0, h1, h2, h3, absurd hk (by omega)]

/-! ## Straight-line blocks -/

variable {C : CallRel} {rd : Reader} {σ : Val}

theorem holdsList_atoms (as : List Atom) (rest : List Stmt) (next : Prop)
    (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (as.map .atom ++ rest) next kret ↔
      (∀ a ∈ as, a.Holds rd σ) ∧ Stmt.HoldsList C rd σ rest next kret := by
  induction as with
  | nil => simp
  | cons a as ih =>
      simp only [List.map_cons, List.cons_append, Stmt.HoldsList, Stmt.Holds, ih,
        List.forall_mem_cons]
      tauto

theorem holdsList_ret (vs : List V) (next : Prop) (rets : List E) :
    Stmt.HoldsList C rd σ [.ret vs] next (fun rs => rs = rets) ↔ vs.map σ = rets := Iff.rfl

@[simp] theorem forall_mem_nil_iff {α : Type} (P : α → Prop) : (∀ x ∈ ([] : List α), P x) ↔ True :=
  ⟨fun _ => trivial, fun _ _ h => absurd h List.not_mem_nil⟩

theorem forall_mem_flatMap_range {α : Type} (n : ℕ) (f : ℕ → List α) (P : α → Prop) :
    (∀ a ∈ (List.range n).flatMap f, P a) ↔ ∀ i < n, ∀ a ∈ f i, P a := by
  simp only [List.mem_flatMap, List.mem_range]
  constructor
  · intro h i hi a ha
    exact h a ⟨i, hi, ha⟩
  · rintro h a ⟨i, hi, ha⟩
    exact h i hi a ha

/-- A run of `k·n` indices, cut into `n` runs of `k`. -/
theorem flatMap_range_mul {α : Type} (k : ℕ) (g : ℕ → List α) :
    ∀ n, (List.range (k * n)).flatMap g =
      (List.range n).flatMap fun b => (List.range k).flatMap fun r => g (k * b + r)
  | 0 => by simp
  | n + 1 => by
      rw [show k * (n + 1) = k * n + k by ring, List.range_add, List.flatMap_append,
        flatMap_range_mul k g n, List.range_succ, List.flatMap_append, List.flatMap_map]
      simp

/-- A list read back by index. -/
theorem flatMap_range_getD {α β : Type} (l : List α) (d : α) (f : α → List β) :
    (List.range l.length).flatMap (fun i => f (l.getD i d)) = l.flatMap f := by
  have : (List.range l.length).map (fun i => l.getD i d) = l := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [List.getElem?_eq_getElem h2]
  conv_rhs => rw [← this]
  rw [List.flatMap_map]

theorem ite_neg' {α : Sort*} {c : Prop} [Decidable c] (h : ¬c) (a b : α) :
    (if c then a else b) = b := by simp [h]

theorem ite_pos' {α : Sort*} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

/-- A valuation listed by value index. -/
def listVal (vs : List E) : Val := fun v => vs.getD v.idx 0

/-- Return-free blocks indexed by `i < n`, then the rest. -/
theorem holdsList_flatMap {C : CallRel} {rd : Reader} {σ : Val} (n : ℕ) (f : ℕ → List Stmt)
    (hf : ∀ i, Stmt.noRetList (f i) = true) (rest : List Stmt) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ ((List.range n).flatMap f ++ rest) next kret ↔
      (∀ i < n, Stmt.HoldsList C rd σ (f i) True kret) ∧ Stmt.HoldsList C rd σ rest next kret := by
  rw [holdsList_append, List.flatMap_def, holdsList_flatten _ (fun b hb => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb; exact hf i)]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

/-! ## Finding a core function -/

/-- A function's relation, unfolded: its body under `Program.Rel`. -/
theorem rel_of_find {f : String} {fn : Fn} (h : coreProgram.find? f = some fn)
    (args rets : List E) :
    coreProgram.Rel rd f args rets ↔ fn.Sem (coreProgram.Rel rd) rd args rets := by
  rw [rel_iff]
  constructor
  · rintro ⟨fn', h', hs⟩
    rw [h] at h'
    cases h'
    exact hs
  · exact fun hs => ⟨fn, h, hs⟩

/-! ## Chains of compressions -/

/-- `n` compressions from `h`, block `i` under the metadata cell `md i`: what a run of `BLAKE2S`
instructions chained through their outputs computes. -/
def chainRun (h : Digest) (blocks : ℕ → Fin 4 → E) (md : ℕ → E) : ℕ → Digest
  | 0 => h
  | i + 1 =>
      compress (chainRun h blocks md i) (blockWords (blockBytes (blocks i)))
        (unpackMetadata (md i)).1 (unpackMetadata (md i)).2.1 (unpackMetadata (md i)).2.2

theorem chainRun_congr {h : Digest} {b b' : ℕ → Fin 4 → E} {md md' : ℕ → E} :
    ∀ n, (∀ i < n, b i = b' i) → (∀ i < n, md i = md' i) →
      chainRun h b md n = chainRun h b' md' n
  | 0, _, _ => rfl
  | n + 1, hb, hm => by
      rw [chainRun, chainRun, chainRun_congr n (fun i hi => hb i (by omega))
        (fun i hi => hm i (by omega)), hb n (by omega), hm n (by omega)]

/-- The guest's `BLAKE2S_IV_0` and `BLAKE2S_IV_1` words are the IV's cells. -/
theorem iv0_word : word 13503953895743350343 11912009169889063794 0 = (digestScalars paramIv).1 := by
  simp only [digestScalars, wordsCell, word, ofLimbs_inj]
  decide

theorem iv1_word : word 11170449402626986623 6620516960021240235 0 = (digestScalars paramIv).2 := by
  simp only [digestScalars, wordsCell, word, ofLimbs_inj]
  decide

/-- A metadata word with a compile-time counter and flag. -/
theorem word_metadata (c : ℕ) (f : Prop) [Decidable f] :
    word c (if f then 4294967295 else 0) 0 = metadataCell c (decide f) := by
  by_cases hf : f <;> simp [hf] <;> rfl

/-- Four cells of a block, listed. -/
theorem block_eta (b : Fin 4 → E) : ![b 0, b 1, b 2, b 3] = b := by
  funext r
  fin_cases r <;> rfl

/-- One `BLAKE2S` of the chain, over canonical cells: its output is the next state. -/
theorem compressCells_chainRun {h : Digest} {blocks : ℕ → Fin 4 → E} {md : ℕ → E} {i : ℕ}
    {o0 o1 : E} (hm : ∀ r, IsCanonical128 (blocks i r)) (hmd : IsCanonical128 (md i)) :
    CompressCells (blocks i) (digestScalars (chainRun h blocks md i)).1
        (digestScalars (chainRun h blocks md i)).2 o0 o1 (md i) ↔
      (o0, o1) = digestScalars (chainRun h blocks md (i + 1)) :=
  compressCells_iff hm hmd

/-- The cells of a `BLAKE2S` are canonical. -/
theorem compressCells_canonical {m : Fin 4 → E} {cv0 cv1 o0 o1 md : E}
    (h : CompressCells m cv0 cv1 o0 o1 md) :
    (∀ r, IsCanonical128 (m r)) ∧ IsCanonical128 md := ⟨h.1, h.2.2.2.2.2.1⟩

/-- The digest of two canonical cells. -/
def cellsDigest (a b : E) : Digest := cellWords a ++ cellWords b

theorem digestScalars_cellsDigest {a b : E} (ha : IsCanonical128 a) (hb : IsCanonical128 b) :
    digestScalars (cellsDigest a b) = (a, b) :=
  (pair_eq_digestScalars_iff.mpr ⟨ha, hb, rfl⟩).symm

/-- A run of `BLAKE2S`s chained from `digestScalars h` computes `chainRun`. -/
theorem chain_eq_chainRun {n : ℕ} {h : Digest} {blocks : ℕ → Fin 4 → E} {md : ℕ → E}
    {st : ℕ → E × E} (h0 : st 0 = digestScalars h)
    (hc : ∀ j < n, CompressCells (blocks j) (st j).1 (st j).2 (st (j + 1)).1 (st (j + 1)).2 (md j)) :
    ∀ j ≤ n, st j = digestScalars (chainRun h blocks md j) := by
  intro j hj
  induction j with
  | zero => exact h0
  | succ j ih =>
      have hcj := hc j (by omega)
      rw [ih (by omega)] at hcj
      have := compressCells_eq hcj
      rw [Prod.mk.eta] at this
      exact this

theorem digestScalars_injective : Function.Injective digestScalars := by
  intro a b h
  have ha := digestOfScalars_digestScalars a
  rw [h, digestOfScalars_digestScalars b] at ha
  exact (Option.some.inj ha).symm

/-- Non-final blocks at counters `t + 64·(j + 1)` are `absorbBlocks`. -/
theorem chainRun_nonfinal {h : Digest} {blocks : ℕ → Fin 4 → E} {md : ℕ → E} {t : ℕ} :
    ∀ n, (∀ j < n, md j = metadataCell (t + 64 * (j + 1)) false) →
      chainRun h blocks md n = absorbBlocks h t ((List.range n).map fun j => blockBytes (blocks j))
  | 0, _ => rfl
  | n + 1, hmd => by
      rw [chainRun, chainRun_nonfinal n (fun j hj => hmd j (by omega)), hmd n (by omega),
        unpackMetadata_metadataCell, List.range_succ, List.map_append, absorbBlocks_append,
        List.length_map, List.length_range, List.map_singleton, absorbBlocks, absorbBlocks]
      simp only [Bool.false_eq_true, ↓reduceIte]
      ring_nf

/-- `n` non-final blocks at counters `64·(j + 1)` and a last block at `64·(n + 1)` with the flag,
from the IV, are `blake2sBytes` of their bytes. -/
theorem chainRun_blocks {blocks : ℕ → Fin 4 → E} {md : ℕ → E} {n : ℕ}
    (hm : ∀ j ≤ n, ∀ r, IsCanonical128 (blocks j r))
    (hmd : ∀ j < n, md j = metadataCell (64 * (j + 1)) false)
    (hfin : md n = metadataCell (64 * (n + 1)) true) :
    chainRun paramIv blocks md (n + 1) =
      blake2sBytes ((List.range (n + 1)).flatMap fun j => blockBytes (blocks j)) := by
  have hcan : ∀ j ≤ n, IsCanonical128 (md j) := by
    intro j hj
    rcases Nat.lt_or_eq_of_le hj with h | h
    · rw [hmd j h]; exact isCanonical128_metadataCell _ _
    · rw [h, hfin]; exact isCanonical128_metadataCell _ _
  have := chain_eq_blake2sBytes_blocks (st := fun j => digestScalars (chainRun paramIv blocks md j))
    rfl hmd hfin (fun j hj => (compressCells_chainRun (hm j hj) (hcan j hj)).mpr rfl)
  exact digestScalars_injective this

/-! ## Chains of `BLAKE2S` over cells, as relations -/

/-- `n` chained `BLAKE2S` instructions from the cells `st` to the cells `out`: none, or a run from
a digest's cells over canonical blocks and metadata cells, computing `chainRun`. -/
def ChainCells (st : E × E) (blocks : ℕ → Fin 4 → E) (md : ℕ → E) (n : ℕ) (out : E × E) : Prop :=
  (n = 0 ∧ out = st) ∨ (1 ≤ n ∧ ∃ h, st = digestScalars h ∧
    (∀ j < n, (∀ r, IsCanonical128 (blocks j r)) ∧ IsCanonical128 (md j)) ∧
    out = digestScalars (chainRun h blocks md n))

/-- A run of chained `BLAKE2S` facts is a `ChainCells`. -/
theorem chainCells_of_steps {n : ℕ} {blocks : ℕ → Fin 4 → E} {md : ℕ → E} {st : ℕ → E × E}
    (hc : ∀ j < n, CompressCells (blocks j) (st j).1 (st j).2 (st (j + 1)).1 (st (j + 1)).2 (md j)) :
    ChainCells (st 0) blocks md n (st n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Or.inl ⟨rfl, rfl⟩
  · have h0 := hc 0 hn
    have hst : st 0 = digestScalars (cellsDigest (st 0).1 (st 0).2) :=
      (digestScalars_cellsDigest h0.2.1 h0.2.2.1).symm
    refine Or.inr ⟨hn, _, hst, fun j hj => compressCells_canonical (hc j hj), ?_⟩
    exact chain_eq_chainRun hst hc n le_rfl

/-- The chained `BLAKE2S` facts of a `ChainCells` run, at the honest states. -/
theorem steps_of_chainCells {n : ℕ} {blocks : ℕ → Fin 4 → E} {md : ℕ → E} {h : Digest}
    (hc : ∀ j < n, (∀ r, IsCanonical128 (blocks j r)) ∧ IsCanonical128 (md j)) :
    ∀ j < n, CompressCells (blocks j) (digestScalars (chainRun h blocks md j)).1
      (digestScalars (chainRun h blocks md j)).2 (digestScalars (chainRun h blocks md (j + 1))).1
      (digestScalars (chainRun h blocks md (j + 1))).2 (md j) := fun j hj =>
  (compressCells_chainRun (hc j hj).1 (hc j hj).2).mpr rfl

theorem chainCells_congr {st out : E × E} {b b' : ℕ → Fin 4 → E} {md md' : ℕ → E} {n : ℕ}
    (hb : ∀ j < n, b j = b' j) (hm : ∀ j < n, md j = md' j) :
    ChainCells st b md n out ↔ ChainCells st b' md' n out := by
  unfold ChainCells
  have e : ∀ h, chainRun h b md n = chainRun h b' md' n := fun h => chainRun_congr n hb hm
  simp only [e]
  constructor
  · rintro (h | ⟨h1, h, h2, h3, h4⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, h, h2, fun j hj => by rw [← hb j hj, ← hm j hj]; exact h3 j hj, h4⟩
  · rintro (h | ⟨h1, h, h2, h3, h4⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, h, h2, fun j hj => by rw [hb j hj, hm j hj]; exact h3 j hj, h4⟩

/-- The block `j` of a list of cells: cells `4j .. 4j + 3`. -/
def blocksOf (cs : List E) (j : ℕ) : Fin 4 → E :=
  ![cs.getD (4 * j) 0, cs.getD (4 * j + 1) 0, cs.getD (4 * j + 2) 0, cs.getD (4 * j + 3) 0]

/-! ## Pointers -/

theorem isInK_mul_gen_pow_iff (p : E) (j : ℕ) : IsInK (p * gen ^ j) ↔ IsInK p := by
  rw [gen_pow_eq_ofK]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (isInK_iff _).mp h
    have hg : Parameters.gpow j ≠ 0 := pow_ne_zero _ g_ne_zero
    refine (isInK_iff _).mpr ⟨a * (Parameters.gpow j)⁻¹, ?_⟩
    rw [ofK_mul, ← ha, mul_assoc, ← ofK_mul, mul_inv_cancel₀ hg, ofK_one, mul_one]
  · intro h
    obtain ⟨a, rfl⟩ := (isInK_iff _).mp h
    rw [← ofK_mul]; exact ofK_isInK _

/-- A load through `p·g^j` at offset `k` is the load through `p` at offset `j + k`. -/
theorem loadHolds_mul_gen_pow {rd : Reader} (p : E) (j k : ℕ) (w : E) :
    LoadHolds rd (p * gen ^ j) k w ↔ LoadHolds rd p (j + k) w := by
  unfold LoadHolds
  rw [isInK_mul_gen_pow_iff]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    obtain ⟨a, rfl⟩ := (isInK_iff _).mp hp
    rw [gen_pow_eq_ofK, ← ofK_mul, limb_ofK] at h
    rw [limb_ofK]
    simp only [Fin.val_zero, ↓reduceIte, Parameters.gpow, pow_add, mul_assoc] at h ⊢
    exact h
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    obtain ⟨a, rfl⟩ := (isInK_iff _).mp hp
    rw [gen_pow_eq_ofK, ← ofK_mul, limb_ofK]
    rw [limb_ofK] at h
    simp only [Fin.val_zero, ↓reduceIte, Parameters.gpow, pow_add, mul_assoc] at h ⊢
    exact h

/-- The word at `p·g^i`, read off the memory (zero where there is none). -/
noncomputable def cellAt (rd : Reader) (p : E) (i : ℕ) : E := (rd (p.limb 0 * Parameters.gpow i)).getD 0

theorem cellAt_of_load {rd : Reader} {p : E} {i : ℕ} {v : E} (h : LoadHolds rd p i v) :
    cellAt rd p i = v := by
  unfold cellAt; rw [h.2]; rfl

theorem load_cellAt {rd : Reader} {p : E} {i : ℕ} {v : E} (h : LoadHolds rd p i v) :
    LoadHolds rd p i (cellAt rd p i) := by
  rwa [cellAt_of_load h]

/-- Cells read through `p·g^b` are the memory's cells from `b` on. -/
theorem cellsAt_slice {rd : Reader} {p : E} {b : ℕ} {cs : List E} (h : CellsAt rd (p * gen ^ b) cs) :
    ∀ k (hk : k < cs.length), cs[k] = cellAt rd p (b + k) ∧ LoadHolds rd p (b + k) (cellAt rd p (b + k)) := by
  intro k hk
  have := (loadHolds_mul_gen_pow p b k _).mp (h k hk)
  exact ⟨(cellAt_of_load this).symm, load_cellAt this⟩

theorem pow4_eq (x : E) (q : ℕ) (hx : x = gen ^ q) : x * x * (x * x) = gen ^ (4 * q) := by
  subst hx; ring

theorem gen_pow_inj' {a b : ℕ} (ha : a < 2 ^ 33) (hb : b < 2 ^ 33) (h : gen ^ a = gen ^ b) : a = b :=
  gen_pow_inj (by omega) (by omega) h

theorem gen_pow_ne_one {r : ℕ} (h1 : 1 ≤ r) (h2 : r < 2 ^ 33) : gen ^ r + 1 ≠ 0 := by
  intro h
  have := (gen_pow_eq_one_iff (by omega)).mp (e_add_eq_zero_iff.mp h)
  omega

/-! ## `mul_range` loops -/

/-- **A `mul_range` loop helper** from `g^k` to its end `N`: its relation holds exactly when `N`
is `g^m` for the first `m > k` the loop reaches, its body (`B`, under the program's relation)
holding at every `g^j`, `k ≤ j < m`. -/
theorem loop_iff {rd : Reader} {f : String} {ps : List E} {N : E} {B : CallRel → E → Prop}
    (hmono : ∀ C C' x, CallRel.Le C C' → B C x → B C' x)
    (hstep : ∀ C x, (∃ fn, coreProgram.find? f = some fn ∧ fn.Sem C rd (x :: ps) []) ↔
      B C x ∧ IsInK (x * gen + N) ∧ (x * gen + N ≠ 0 → C f (x * gen :: ps) []))
    (k : ℕ) :
    coreProgram.Rel rd f (gen ^ k :: ps) [] ↔
      ∃ m, k < m ∧ N = gen ^ m ∧ (∀ j, k < j → j < m → gen ^ j ≠ N) ∧
        ∀ j, k ≤ j → j < m → B (coreProgram.Rel rd) (gen ^ j) := by
  have hadd : ∀ j, gen ^ j * gen + N = 0 ↔ N = gen ^ (j + 1) := fun j => by
    rw [e_add_eq_zero_iff, pow_succ, eq_comm]
  constructor
  · rintro ⟨d, hd⟩
    induction d generalizing k with
    | zero => exact hd.elim
    | succ d ih =>
      obtain ⟨hB, -, hnext⟩ := (hstep _ _).mp hd
      have hB' := hmono _ _ _ (relN_le_rel coreProgram d) hB
      by_cases h0 : gen ^ k * gen + N = 0
      · refine ⟨k + 1, by omega, (hadd k).mp h0, fun j h1 h2 => by omega, fun j h1 h2 => ?_⟩
        rwa [show j = k by omega]
      · have := hnext h0
        rw [← pow_succ] at this
        obtain ⟨m, hm, hN, hfirst, hall⟩ := ih (k + 1) this
        refine ⟨m, by omega, hN, fun j h1 h2 => ?_, fun j h1 h2 => ?_⟩
        · rcases Nat.lt_or_ge (k + 1) j with h | h
          · exact hfirst j h h2
          · rw [show j = k + 1 by omega]
            intro he
            exact h0 ((hadd k).mpr he.symm)
        · rcases Nat.lt_or_ge k j with h | h
          · exact hall j (by omega) h2
          · rwa [show j = k by omega]
  · rintro ⟨m, hkm, hN, hfirst, hall⟩
    obtain ⟨t, rfl⟩ : ∃ t, m = k + 1 + t := ⟨m - k - 1, by omega⟩
    have hK : ∀ j, IsInK (gen ^ j * gen + N) := fun j => by
      rw [hN, ← pow_succ, gen_pow_eq_ofK, gen_pow_eq_ofK, ← ofK_add]; exact ofK_isInK _
    induction t generalizing k with
    | zero =>
      rw [rel_iff]
      exact (hstep _ _).mpr ⟨hall k le_rfl (by omega), hK k,
        fun h => absurd ((hadd k).mpr hN) h⟩
    | succ t ih =>
      rw [rel_iff]
      refine (hstep _ _).mpr ⟨hall k le_rfl (by omega), hK k, fun _ => ?_⟩
      rw [← pow_succ]
      exact ih (k + 1) (by omega) (by rw [hN]; congr 1; omega)
        (fun j h1 h2 => hfirst j (by omega) (by omega)) (fun j h1 h2 => hall j (by omega) (by omega))

end
end LeanVM.Guest.B1.Digest
