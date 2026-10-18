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

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-! ## The memory -/

/-- The reader is a memory of `2^κ` words, `16 ≤ κ ≤ 32`, as every valid execution's is. -/
def MemOk (rd : Reader) : Prop := ∃ κ, 16 ≤ κ ∧ κ ≤ 32 ∧ ∃ L : MemImage κ, rd = L.read

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

/-- A word with zero upper limbs is the integer word. -/
theorem word_eq_eOfNat (c : ℕ) : word c 0 0 = eOfNat c := by
  rw [eOfNat_eq_ofLimbs]; rfl

theorem isCanonical128_zero : IsCanonical128 (0 : E) := by
  rw [zero_eq_ofLimbs]; rfl

theorem word_zero : word 0 0 0 = 0 := by rw [word_eq_eOfNat, eOfNat_zero]

/-- `INV_GEN`, the word the guest multiplies a runtime range bound by. -/
theorem ginv_mul_gen : word 9223372036854775821 0 0 * gen = 1 := by
  rw [word_eq_eOfNat, gen, eOfNat, eOfNat, ← ofK_mul, ← ofK_one]
  congr 1

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

end
end LeanVM.Guest.B1
