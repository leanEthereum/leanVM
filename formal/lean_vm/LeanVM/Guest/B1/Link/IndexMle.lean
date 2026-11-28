/-
  LeanVM.Guest.B1.Link.IndexMle

  B1 for `index_mle` at the link's widths (`19` to `24`): `indexMle` of the point.
-/

module

public import LeanVM.Guest.B1.Link.IndexSide
public import LeanVM.Guest.Value.Tower

/-!
# `index_mle` at the link's widths

`index_mle(zeta, n)` (G, unchanged since the bus era) multiplies `1 + zeta[t]·INDEX_MLE_FACTORS[t]`
over `t < n`, `INDEX_MLE_FACTORS[t] = 1 + g^(2^t)`. The bus era's B1 (`B1/Selectors/IndexMle.lean`,
tag `formal-bus-archive`) restated on this branch's infrastructure, at the widths `index_side`
calls: `index_mle__L{n}` is `imBody n`, block `t` from value `6 t` (`imBlk`), the first without
the product. The factors' words are the squares of `g` (`gSquaresBits`, by kernel evaluation of
repeated squaring). This discharges `IndexMleSound` (`index_mle_holds`).
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The squares of `g` -/

/-- `x, x², x⁴, …`, `n` terms, one squaring an entry. -/
def squaresL {R : Type} [Mul R] : ℕ → R → List R
  | 0, _ => []
  | n + 1, x => x :: squaresL n (x * x)

theorem length_squaresL {R : Type} [Mul R] (n : ℕ) (x : R) : (squaresL n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [squaresL, ih]

theorem getElem_squaresL {R : Type} [Monoid R] (n : ℕ) (x : R) (j : ℕ)
    (hj : j < (squaresL n x).length) : (squaresL n x)[j] = x ^ 2 ^ j := by
  induction n generalizing x j with
  | zero => simp [squaresL] at hj
  | succ n ih =>
    cases j with
    | zero => simp [squaresL]
    | succ j =>
      simp only [squaresL, List.getElem_cons_succ]
      rw [ih (x * x) j (by simpa [squaresL] using hj), ← sq, ← pow_mul, pow_succ, Nat.mul_comm]

/-- `g^(2^j)` for `j < 34`, as 64-bit words. -/
def gSquaresBits : List ℕ := [
  0x2, 0x4, 0x10, 0x100, 0x10000, 0x100000000, 0x1b, 0x145, 0x11011, 0x101000101,
  0x100000001001a, 0x1a00000144, 0x10dbc, 0x100514550, 0x11011011111b, 0x10001011a1a015e,
  0x15f0144001a114f, 0x1aad43011ba1e5, 0x11cefef6be466, 0x5455145e48670f13,
  0xbaf1bebe1ae4ad02, 0xb0ef530df44bb042, 0xe2170b43ee771735, 0x48380fd207a3b527,
  0xb6d535c542116f62, 0xa6df6baa62f965f5, 0xb9df3947cea0ffe7, 0xe1882807248fe588,
  0x180d86953ed141c6, 0x1894566cd1db8abf, 0x4cc78bf4ea999e25, 0xe333308087e402ba,
  0x5c62236777028505, 0xb964dc682c67ddcd]

theorem gSquaresBits_eq : gSquaresBits.map K.ofBits = squaresL 34 g := by decide +kernel

/-- **`g^(2^j)`**, `j < 34`, is the word `gSquaresBits[j]`. -/
theorem gen_pow_two_pow_word {j : ℕ} (hj : j < 34) : gen ^ 2 ^ j = eOfNat (gSquaresBits.getD j 0) := by
  have h := congrArg (fun l : List K ↦ l[j]?) gSquaresBits_eq
  have hj1 : j < gSquaresBits.length := by rw [show gSquaresBits.length = 34 from rfl]; exact hj
  have hj2 : j < (squaresL 34 g).length := by rw [length_squaresL]; exact hj
  simp only [List.getElem?_map, List.getElem?_eq_getElem hj1, List.getElem?_eq_getElem hj2,
    Option.map_some, Option.some.injEq, getElem_squaresL] at h
  rw [eOfNat, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj1, Option.getD_some, h, ofK_pow]
  rfl

/-! ## The template -/

/-- `INDEX_MLE_FACTORS[t]`: the word of `1 + g^(2^t)`. -/
def imFactor (t : ℕ) : ℕ := gSquaresBits.getD t 0 ^^^ 1

theorem imFactor_eq {t : ℕ} (ht : t < 34) : word (imFactor t) 0 = 1 + gen ^ 2 ^ t := by
  rw [word_eOfNat, imFactor, eOfNat_xor, eOfNat_one, gen_pow_two_pow_word ht, add_comm]

/-- Block `t`: the factor, times the running product (from value `6 t`). -/
def imBlk (t : ℕ) : List Stmt :=
  if t = 0 then
    [.atom (.const (.n 1) (word 1 0)), .atom (.load (.n 2) (.n 0) 0),
      .atom (.const (.n 3) (word (imFactor 0) 0)), .atom (.mul (.n 4) (.n 2) (.n 3)),
      .atom (.add (.n 5) (.n 1) (.n 4))]
  else
    [.atom (.const (.n (6 * t)) (word 1 0)), .atom (.load (.n (6 * t + 1)) (.n 0) t),
      .atom (.const (.n (6 * t + 2)) (word (imFactor t) 0)),
      .atom (.mul (.n (6 * t + 3)) (.n (6 * t + 1)) (.n (6 * t + 2))),
      .atom (.add (.n (6 * t + 4)) (.n (6 * t)) (.n (6 * t + 3))),
      .atom (.mul (.n (6 * t + 5)) (.n (6 * t - 1)) (.n (6 * t + 4)))]

/-- The expansion of `index_mle__L{n}`, `n ≥ 1`. -/
def imBody (n : ℕ) : List Stmt :=
  ((List.range n).map imBlk).flatten ++ [.atom (.copy (.n (6 * n)) (.n (6 * n - 1))), .ret [.n (6 * n)]]

theorem imBlk_noRet (t : ℕ) : Stmt.noRetList (imBlk t) = true := by
  unfold imBlk; split <;> rfl

/-- The factor of coordinate `t`. -/
def imFactorOf (r : E) (t : ℕ) : E := 1 + r * (1 + gen ^ 2 ^ t)

/-- The load and the product of block `t`. -/
def imLoad (t : ℕ) : ℕ := if t = 0 then 2 else 6 * t + 1

def imAcc (t : ℕ) : ℕ := 6 * t + 5

theorem holds_imBlk {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} {t : ℕ} (ht : t < 34)
    (h : Stmt.HoldsList C rd σ (imBlk t) True kret) :
    LoadHolds rd (σ (.n 0)) t (σ (.n (imLoad t))) ∧
      σ (.n (imAcc t)) = (if t = 0 then 1 else σ (.n (imAcc (t - 1)))) * imFactorOf (σ (.n (imLoad t))) t := by
  unfold imBlk at h
  split_ifs at h with h0
  · subst h0
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    refine ⟨h2, ?_⟩
    simp only [imAcc, imLoad, ↓reduceIte, imFactorOf, one_mul]
    rw [h5, h1, h4, h3, word_one, imFactor_eq (by decide)]
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    refine ⟨by simp only [imLoad, h0, ↓reduceIte]; exact h2, ?_⟩
    simp only [imAcc, imLoad, h0, ↓reduceIte, imFactorOf]
    rw [h6, h5, h1, h4, h3, word_one, imFactor_eq ht, show 6 * (t - 1) + 5 = 6 * t - 1 by omega]

/-- `indexMle` as a product of its factors. -/
theorem indexMleFrom_eq (zs : List E) : ∀ (k : ℕ) (acc : E),
    indexMleFrom (gen ^ 2 ^ k) zs acc =
      acc * prodE ((List.range zs.length).map fun t ↦ imFactorOf (zs.getD t 0) (k + t)) := by
  induction zs with
  | nil => intro k acc; simp [indexMleFrom, prodE]
  | cons r rs ih =>
    intro k acc
    rw [indexMleFrom, show (gen ^ 2 ^ k) ^ 2 = gen ^ 2 ^ (k + 1) by rw [← pow_mul, pow_succ],
      ih (k + 1), List.length_cons, List.range_succ_eq_map, List.map_cons, prodE_cons, List.map_map]
    have hf : ((fun t ↦ imFactorOf ((r :: rs).getD t 0) (k + t)) ∘ fun t ↦ t + 1) =
        fun t ↦ imFactorOf (rs.getD t 0) (k + 1 + t) := by
      funext t
      rw [Function.comp_apply, List.getD_cons_succ, show k + (t + 1) = k + 1 + t by omega]
    rw [hf, List.getD_cons_zero, imFactorOf, mul_assoc]
    rfl

theorem indexMle_eq_prodE (zs : List E) :
    indexMle zs = prodE ((List.range zs.length).map fun t ↦ imFactorOf (zs.getD t 0) t) := by
  have := indexMleFrom_eq zs 0 1
  rw [pow_zero, pow_one] at this
  rw [indexMle, this, one_mul]
  simp

/-- **The template's relation implies its meaning.** -/
theorem im_sound (n : ℕ) (hn : 1 ≤ n ∧ n < 34) {f : Fn}
    (hfind : coreProgram.find? (imNames.getD (n - 19) "") = some f) (hparams : f.params = [.n 0])
    (hbody : f.body = imBody n) (rd : Reader) (zeta v : E) :
    coreProgram.Rel rd (imNames.getD (n - 19) "") [zeta] [v] →
      ∃ zs : List E, zs.length = n ∧ ReadsAt rd zeta zs ∧ v = indexMle zs := by
  rw [rel_iff_sem hfind, hbody, hparams, imBody]
  simp only [holdsList_append, holdsList_range_flatten n imBlk imBlk_noRet, Stmt.HoldsList,
    Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
  rintro ⟨σ, hpar, hblk, hcopy, hret⟩
  simp only [List.cons.injEq, and_true] at hpar hret
  subst hpar hret
  have hb := fun t (ht : t < n) ↦ holds_imBlk (C := coreProgram.Rel rd) (by omega) (hblk t ht)
  let zs := (List.range n).map fun t ↦ σ (.n (imLoad t))
  have hacc : ∀ t < n, σ (.n (imAcc t)) =
      prodE ((List.range (t + 1)).map fun s ↦ imFactorOf (zs.getD s 0) s) := by
    intro t ht
    induction t with
    | zero =>
      rw [(hb 0 ht).2]
      simp [zs, List.getD_eq_getElem?_getD, ht, prodE]
    | succ t ih =>
      rw [(hb (t + 1) ht).2]
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [ih (by omega),
        show List.range (t + 1 + 1) = List.range (t + 1) ++ [t + 1] from List.range_succ,
        List.map_append, prodE_append]
      simp [zs, List.getD_eq_getElem?_getD, ht, prodE]
  refine ⟨zs, by simp [zs], fun t ht => ?_, ?_⟩
  · simp only [zs, List.length_map, List.length_range] at ht
    simpa [zs] using (hb t ht).1
  · rw [hcopy, indexMle_eq_prodE, show 6 * n - 1 = imAcc (n - 1) by simp only [imAcc]; omega,
      hacc (n - 1) (by omega), show n - 1 + 1 = n by omega]
    simp [zs]

/-! ## The specializations -/

set_option maxRecDepth 100000 in
theorem index_mle_L19_sound (rd : Reader) (zeta v : E) :
    coreProgram.Rel rd (imNames.getD 0 "") [zeta] [v] →
      ∃ zs : List E, zs.length = 19 ∧ ReadsAt rd zeta zs ∧ v = indexMle zs :=
  im_sound 19 ⟨by omega, by omega⟩ (f := fn% «index_mle__L19»)
    (coreProgram_find?_at (j := idx% «index_mle__L19») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd zeta v

set_option maxRecDepth 100000 in
theorem index_mle_L20_sound (rd : Reader) (zeta v : E) :
    coreProgram.Rel rd (imNames.getD 1 "") [zeta] [v] →
      ∃ zs : List E, zs.length = 20 ∧ ReadsAt rd zeta zs ∧ v = indexMle zs :=
  im_sound 20 ⟨by omega, by omega⟩ (f := fn% «index_mle__L20»)
    (coreProgram_find?_at (j := idx% «index_mle__L20») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd zeta v

set_option maxRecDepth 100000 in
theorem index_mle_L21_sound (rd : Reader) (zeta v : E) :
    coreProgram.Rel rd (imNames.getD 2 "") [zeta] [v] →
      ∃ zs : List E, zs.length = 21 ∧ ReadsAt rd zeta zs ∧ v = indexMle zs :=
  im_sound 21 ⟨by omega, by omega⟩ (f := fn% «index_mle__L21»)
    (coreProgram_find?_at (j := idx% «index_mle__L21») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd zeta v

set_option maxRecDepth 100000 in
theorem index_mle_L22_sound (rd : Reader) (zeta v : E) :
    coreProgram.Rel rd (imNames.getD 3 "") [zeta] [v] →
      ∃ zs : List E, zs.length = 22 ∧ ReadsAt rd zeta zs ∧ v = indexMle zs :=
  im_sound 22 ⟨by omega, by omega⟩ (f := fn% «index_mle__L22»)
    (coreProgram_find?_at (j := idx% «index_mle__L22») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd zeta v

set_option maxRecDepth 100000 in
theorem index_mle_L23_sound (rd : Reader) (zeta v : E) :
    coreProgram.Rel rd (imNames.getD 4 "") [zeta] [v] →
      ∃ zs : List E, zs.length = 23 ∧ ReadsAt rd zeta zs ∧ v = indexMle zs :=
  im_sound 23 ⟨by omega, by omega⟩ (f := fn% «index_mle__L23»)
    (coreProgram_find?_at (j := idx% «index_mle__L23») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd zeta v

set_option maxRecDepth 100000 in
theorem index_mle_L24_sound (rd : Reader) (zeta v : E) :
    coreProgram.Rel rd (imNames.getD 5 "") [zeta] [v] →
      ∃ zs : List E, zs.length = 24 ∧ ReadsAt rd zeta zs ∧ v = indexMle zs :=
  im_sound 24 ⟨by omega, by omega⟩ (f := fn% «index_mle__L24»)
    (coreProgram_find?_at (j := idx% «index_mle__L24») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd zeta v

/-- **`index_mle`'s meaning at the link's widths**: `IndexMleSound`. -/
theorem index_mle_holds : IndexMleSound coreProgram := by
  intro w h1 h2 rd zeta v
  interval_cases w
  exacts [index_mle_L19_sound rd zeta v, index_mle_L20_sound rd zeta v, index_mle_L21_sound rd zeta v, index_mle_L22_sound rd zeta v, index_mle_L23_sound rd zeta v, index_mle_L24_sound rd zeta v]

end
end LeanVM.Guest.B1.Link
