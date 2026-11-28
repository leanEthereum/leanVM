/-
  LeanVM.Guest.B1.Bits.Tables

  B1 for `exponent_tables`: the read-only exponent table.
-/

module

public import LeanVM.Guest.B1.Bits.Meaning
public import LeanVM.Guest.B1.Common.Find
public import LeanVM.Guest.GuestConst
import LeanVM.Guest.ValRef
import LeanVM.Guest.LitRef
import LeanVM.Guest.Data.Consts
import LeanVM.Guest.Data.ValNames.«exponent_tables»

/-!
# `exponent_tables`

`exponent_tables()` (`lean_ethereum.py`) fills a fresh `HeapBuf(178 + 2^11)` with constants the
compiler folds: `expTabN` pairs `const`, `load`, in offset order: the squares `0 .. 33`, the nibble
shares `34 .. 177`, the bit windows `178 + n`. The first `178` words (`etWordsN`) are the honest
values in `K`, decided by the kernel over `etListK`, which computes them as the source does, one
product a word: `squares`, `nibRuns` (`powRun` sixteen at a time); window `n`'s word is `n`.

* `exponent_tables_holds`: its core IR is its meaning (`ExpTables` and `ExpWinTab`,
  `Guest/ExpTables.lean`).
* `expTables_iff_words`: `ExpTables` is the `178` words `expTableWords` at the pointer;
  `expTabAll_iff`: with `ExpWinTab`, the `expTabN` words `expTabAllWords`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Runs of products -/

/-- `n` successive squares from `x`: `x, x², x⁴, …`, as `sq_run *= sq_run` computes them. -/
def squares {R : Type} [Mul R] : ℕ → R → List R
  | 0, _ => []
  | n + 1, x => x :: squares n (x * x)

theorem length_squares {R : Type} [Mul R] (n : ℕ) (x : R) : (squares n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [squares, ih]

/-- Entry `j` of the squares from `x` is `x^(2^j)`. -/
theorem getElem_squares {R : Type} [Monoid R] (n : ℕ) (x : R) (j : ℕ)
    (hj : j < (squares n x).length) : (squares n x)[j] = x ^ 2 ^ j := by
  induction n generalizing x j with
  | zero => simp [squares] at hj
  | succ n ih =>
    cases j with
    | zero => simp [squares]
    | succ j =>
      simp only [squares, List.getElem_cons_succ]
      rw [ih (x * x) j (by simpa [squares] using hj), ← sq, ← pow_mul, pow_succ, Nat.mul_comm]

/-- `n` successive products by `b` from `s`: `s, s·b, s·b², …` (`share *= base`). -/
def powRun {R : Type} [Mul R] (b : R) : ℕ → R → List R
  | 0, _ => []
  | n + 1, s => s :: powRun b n (s * b)

theorem length_powRun {R : Type} [Mul R] (b : R) (n : ℕ) (s : R) : (powRun b n s).length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [powRun, ih]

theorem getElem_powRun {R : Type} [Monoid R] (b : R) (n : ℕ) (s : R) (i : ℕ)
    (hi : i < (powRun b n s).length) : (powRun b n s)[i] = s * b ^ i := by
  induction n generalizing s i with
  | zero => simp [powRun] at hi
  | succ n ih =>
    cases i with
    | zero => simp [powRun]
    | succ i =>
      simp only [powRun, List.getElem_cons_succ]
      rw [ih (s * b) i (by simpa [powRun] using hi), pow_succ', mul_assoc]

/-- The nibble shares from the base `b`: sixteen powers of `b`, then of `b^16`, … -/
def nibRuns {R : Type} [Monoid R] (b : R) : ℕ → List R
  | 0 => []
  | j + 1 => powRun b 16 1 ++ nibRuns (b ^ 16) j

theorem length_nibRuns {R : Type} [Monoid R] (b : R) (j : ℕ) : (nibRuns b j).length = 16 * j := by
  induction j generalizing b with
  | zero => rfl
  | succ j ih => simp [nibRuns, ih, length_powRun]; omega

theorem getElem_nibRuns {R : Type} [Monoid R] (b : R) (J j u : ℕ) (hj : j < J) (hu : u < 16)
    (h : 16 * j + u < (nibRuns b J).length) : (nibRuns b J)[16 * j + u] = b ^ (u * 16 ^ j) := by
  induction J generalizing b j with
  | zero => omega
  | succ J ih =>
    simp only [nibRuns]
    cases j with
    | zero =>
      rw [List.getElem_append_left (by rw [length_powRun]; omega)]
      simp [getElem_powRun]
    | succ j =>
      rw [List.getElem_append_right (by rw [length_powRun]; omega)]
      simp only [length_powRun]
      have e : 16 * (j + 1) + u - 16 = 16 * j + u := by omega
      simp only [e]
      rw [ih (b ^ 16) j (by omega) (by rw [length_nibRuns] at h ⊢; omega), ← pow_mul, pow_succ]
      congr 1
      ring

/-! ## The table's words -/

/-- The table's honest words in `K`, by offset, computed as the source does. -/
def etListK : List K := squares 34 g ++ nibRuns g 9

/-- The table's words, by offset, as the compiler folds them. -/
def etWordsN : List ℕ := [
  2, 4, 0x10, 0x100, 0x10000, 0x100000000, 0x1b, 0x145, 0x11011, 0x101000101, 0x100000001001a,
  0x1a00000144, 0x10dbc, 0x100514550, 0x11011011111b, 0x10001011a1a015e, 0x15f0144001a114f,
  0x1aad43011ba1e5, 0x11cefef6be466, 0x5455145e48670f13, 0xbaf1bebe1ae4ad02, 0xb0ef530df44bb042,
  0xe2170b43ee771735, 0x48380fd207a3b527, 0xb6d535c542116f62, 0xa6df6baa62f965f5,
  0xb9df3947cea0ffe7, 0xe1882807248fe588, 0x180d86953ed141c6, 0x1894566cd1db8abf,
  0x4cc78bf4ea999e25, 0xe333308087e402ba, 0x5c62236777028505, 0xb964dc682c67ddcd, 1, 2, 4, 8, 0x10,
  0x20, 0x40, 0x80, 0x100, 0x200, 0x400, 0x800, 0x1000, 0x2000, 0x4000, 0x8000, 1, 0x10000,
  0x100000000, 0x1000000000000, 0x1b, 0x1b0000, 0x1b00000000, 0x1b000000000000, 0x145, 0x1450000,
  0x14500000000, 0x145000000000000, 0x1db7, 0x1db70000, 0x1db700000000, 0x1db7000000000000, 1,
  0x11011, 0x101000101, 0x1110110110111, 0x100000001001a, 0x10110001100aa1a1, 0x100011a1b1a011a,
  0x100baa100bb1aa0a, 0x1a00000144, 0x1ba1ba01505504, 0x1a001b5f4401441a, 0xa0eb1eea544fee41,
  0x15e0144001a1ce8, 0xf5ee551fbc9d4f5d, 0x1b4543b0eee81b44, 0xb89a98b89a98b894, 1, 0x10dbc,
  0x100514550, 0x10deeff7bf8c0, 0x11011011111b, 0x11d7617607b1dce4, 0x5555155e522c4b1c,
  0x1631292a1c9f84e3, 0x10001011a1a015e, 0xbd0cab0bf4085307, 0x1b092fc78d4a92cc,
  0xaa644ef5214e1933, 0xbbaeaefb0aefad57, 0xe43e44f979305954, 0x1b8c364e2acb3ea9,
  0x561ccc67eda76752, 1, 0x15f0144001a114f, 0x1aad43011ba1e5, 0xe34916e80106e21d, 0x11cefef6be466,
  0xab943b855d3d776b, 0x1c77b6cf4edf1bd0, 0x46923ddea5ce4e34, 0x5455145e48670f13,
  0xfb7d34d8e2b804bb, 0xbbe0dfe164a4d5b4, 0x431d528b1f73a8a2, 0xc259794b79e2607,
  0x5945c54c76a8d132, 0xf5cb8b3860386917, 0xb345180ffd7a5551, 1, 0xbaf1bebe1ae4ad02,
  0xb0ef530df44bb042, 0xe1398cba3a3345d1, 0xe2170b43ee771735, 0xef974077ab2e410a,
  0x195f74d8d767e0ec, 0xe7a9ce1b1009ddf5, 0x48380fd207a3b527, 0x1c041e035dbcddcb,
  0x5f44de92a000c6c2, 0x46349d7a0998e7db, 0x4ccfb81392b73990, 0xb8cfaede33ecc098,
  0x1cc1aa9d264d48e7, 0xb8c0690563b0c7a0, 1, 0xb6d535c542116f62, 0xa6df6baa62f965f5,
  0x43cd877666280ea1, 0xb9df3947cea0ffe7, 0x4914ca4044188719, 0xa464732dc19282c6,
  0xec96d1ac82c47367, 0xe1882807248fe588, 0xfc1a74c733a2f5ce, 0xa6cb1bf736b8b15a,
  0x14653a240571ca31, 0xfdb09cb587733b25, 0x46c5665415338185, 0x5b728acb7e18bf24,
  0x1257c0c0b80081b1, 1, 0x180d86953ed141c6, 0x1894566cd1db8abf, 0xe140c4c3e9685529,
  0x4cc78bf4ea999e25, 0xa4a5d5d6667950d6, 0x485ba44760a67477, 0x130c212db28e3452,
  0xe333308087e402ba, 0x47a0b59555acba5e, 0xb9a2b8ed7bac3b92, 0x17cd2ccc4fbbeca4,
  0xa2c1e9a5b8a1a4c9, 0xb4812ccc0001799e, 0x5e734724690b7a6f, 0x4b4f8209fddb26fb, 1,
  0x5c62236777028505, 0xb964dc682c67ddcd, 0xb8f3ae623e1592a, 0xb58ac9a23d208acb,
  0x1a83edcac97c2423, 0x2b4930660ea1998, 0x12bc2b081f75d26c, 0xb3fcc2ab3699fc73,
  0x1f0ccd02e5018031, 0x4debd5201f7c72a9, 0xfebd6e55fb0a04b, 0x146ae2f2da36409c,
  0xf4cfd90774d917b7, 0x1a3fa5613bb31290, 0xa7c23c08867ab11f]

theorem length_etWordsN : etWordsN.length = 178 := by decide +kernel

/-- **The folded words are the honest values**, decided by the kernel. -/
theorem etWordsN_eq : etWordsN.map K.ofBits = etListK := by decide +kernel

theorem length_etListK : etListK.length = 178 := by rw [← etWordsN_eq, List.length_map]; rfl

/-- The honest words of the table, in `E`. -/
def expTableWords : List E := etWordsN.map eOfNat

theorem expTableWords_getD (o : ℕ) (ho : o < 178) :
    expTableWords.getD o 0 = ofK (etListK[o]'(by rw [length_etListK]; exact ho)) := by
  have h1 : o < etWordsN.length := by rw [length_etWordsN]; exact ho
  have h2 := congrArg (fun l : List K ↦ l[o]?) etWordsN_eq
  simp only [List.getElem?_map, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem (show o < etListK.length by rw [length_etListK]; exact ho),
    Option.map_some, Option.some.injEq] at h2
  rw [expTableWords, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h1,
    Option.map_some, Option.getD_some, eOfNat, h2]

theorem getElem_idx {α : Type} {l : List α} {i j : ℕ} (h : i = j) (hi : i < l.length) :
    l[i] = l[j]'(h ▸ hi) := by
  subst h; rfl

theorem etListK_sq (j : ℕ) (hj : j < 34) : etListK[j]'(by rw [length_etListK]; omega) =
    g ^ 2 ^ j := by
  simp only [etListK]
  rw [List.getElem_append_left (by rw [length_squares]; omega), getElem_squares]

theorem etListK_nib (j u : ℕ) (hj : j < 9) (hu : u < 16) :
    etListK[34 + 16 * j + u]'(by rw [length_etListK]; omega) = g ^ (u * 16 ^ j) := by
  simp only [etListK]
  rw [List.getElem_append_right (by rw [length_squares]; omega),
    getElem_idx (show 34 + 16 * j + u - (squares 34 g).length = 16 * j + u by
      rw [length_squares]; omega)]
  exact getElem_nibRuns g _ j u hj hu _

/-- **The exponent table is its `178` words.** -/
theorem expTables_iff_words (rd : Reader) (q : E) :
    ExpTables rd q ↔ ∀ o < 178, LoadHolds rd q o (expTableWords.getD o 0) := by
  simp only [ExpTables, sizeBits, selTabNibbles]
  constructor
  · rintro ⟨h1, h2⟩ o ho
    rw [expTableWords_getD o ho]
    by_cases a : o < 34
    · rw [etListK_sq o a, ofK_pow, ← gen_eq_ofK]; exact h1 o a
    · obtain ⟨j, u, hj, hu, rfl⟩ : ∃ j u, j < 9 ∧ u < 16 ∧ o = 34 + 16 * j + u :=
        ⟨(o - 34) / 16, (o - 34) % 16, by omega, by omega, by omega⟩
      rw [etListK_nib j u hj hu, ofK_pow, ← gen_eq_ofK]; exact h2 j hj u hu
  · intro h
    refine ⟨fun j hj ↦ ?_, fun j hj u hu ↦ ?_⟩
    · have := h j (by omega)
      rwa [expTableWords_getD j (by omega), etListK_sq j hj, ofK_pow, ← gen_eq_ofK] at this
    · have := h (34 + 16 * j + u) (by omega)
      rwa [expTableWords_getD _ (by omega), etListK_nib j u hj hu, ofK_pow, ← gen_eq_ofK] at this

/-! ## The bit windows -/

/-- The table's honest word at offset `o`: `expTableWords` below `178`, then window `o - 178`. -/
def expTabWord (o : ℕ) : E := if o < 178 then expTableWords.getD o 0 else eOfNat (o - 178)

/-- **The table's size**: its `178` words and the bit windows (`WIN_TAB_AT + WIN_TAB_LEN`), what `main`'s proofs
restate as `lit% B1.expTabN`. -/
def expTabN : ℕ := guest_const% WIN_TAB_AT + guest_const% WIN_TAB_LEN

/-- The whole table's `expTabN` honest words. -/
def expTabAllWords : List E := (List.range lit% expTabN).map expTabWord

theorem length_expTabAllWords : expTabAllWords.length = lit% expTabN := by simp [expTabAllWords]

theorem expTabAllWords_getD (o : ℕ) :
    expTabAllWords.getD o 0 = if o < lit% expTabN then expTabWord o else 0 := by
  by_cases h : o < lit% expTabN <;> simp [expTabAllWords, h]

/-- **The exponent table and its bit windows are its `expTabN` words.** -/
theorem expTabAll_iff (rd : Reader) (q : E) :
    ExpTables rd q ∧ ExpWinTab rd q ↔ ∀ o < lit% expTabN, LoadHolds rd q o (expTabWord o) := by
  rw [expTables_iff_words]
  constructor
  · rintro ⟨h1, h2⟩ o ho
    by_cases a : o < 178
    · rw [expTabWord, ite_pos' a]; exact h1 o a
    · rw [expTabWord, ite_neg' a]
      have := h2 (o - 178) (by simp only [winTabBits]; omega)
      rwa [winTabAt, Nat.add_sub_cancel' (by omega)] at this
  · intro h
    refine ⟨fun o ho ↦ ?_, fun n hn ↦ ?_⟩
    · have := h o (by omega); rwa [expTabWord, ite_pos' ho] at this
    · simp only [winTabBits] at hn
      have := h (178 + n) (by omega)
      rwa [expTabWord, ite_neg' (show ¬178 + n < 178 by omega), Nat.add_sub_cancel_left] at this

/-! ## The function -/

/-- The word body position `t` writes, folded: the squares, then the shares, then the windows, each
at its own offset. -/
def etWord (t : ℕ) : ℕ := if t < 178 then etWordsN.getD t 0 else t - 178

/-- `g_squares[g^t] = w`, folded. -/
def etBlk (t : ℕ) : List Stmt :=
  [.atom (.const (.n (t + 1)) (word (etWord t) 0)), .atom (.load (.n (t + 1)) (.n (val% «exponent_tables» "g_squares")) t)]

/-- The expansion of `exponent_tables`. -/
def etBody : List Stmt :=
  [.atom (.hint (.alloc (.n (val% «exponent_tables» "g_squares")) lit% expTabN))] ++ ((List.range lit% expTabN).map etBlk).flatten ++
  [.atom (.copy (.n (val% «exponent_tables» "s6#0")) (.n (val% «exponent_tables» "g_squares"))), .ret [.n (val% «exponent_tables» "s6#0")]]

theorem exponent_tables_body : Fn.body fn% «exponent_tables» = etBody :=
  stmtsEqb_sound (by decide +kernel)

theorem find_exponent_tables : coreProgram.find? "exponent_tables" = some fn% «exponent_tables» :=
  coreProgram_find?_at (j := idx% «exponent_tables») rfl

/-- The word body position `t` writes is the honest word at its offset. -/
theorem word_etWord (t : ℕ) : word (etWord t) 0 = expTabWord t := by
  rw [word_eOfNat, etWord, expTabWord]
  by_cases a : t < 178
  · rw [ite_pos' a, ite_pos' a, expTableWords, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_map]
    cases etWordsN[t]? <;> simp [eOfNat_zero]
  · rw [ite_neg' a, ite_neg' a]

/-- **`exponent_tables`' core IR is its meaning.** -/
theorem exponent_tables_holds : exponent_tables_Spec := by
  intro rd args rets
  rw [rel_iff_sem find_exponent_tables, exponent_tables_body,
      show Fn.params fn% «exponent_tables» = [] from rfl, etBody]
  simp only [holdsList_append, Stmt.HoldsList]
  simp only [holdsList_range_flatten lit% expTabN etBlk (fun _ => rfl), etBlk]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and,
    and_true]
  simp only [word_etWord]
  constructor
  · rintro ⟨σ, hp, ht, h2227, hret⟩
    subst hp hret
    rw [h2227]
    exact (expTabAll_iff rd _).2 fun t h ↦ by
      obtain ⟨c, l⟩ := ht t h
      rwa [c] at l
  · intro hm
    obtain ⟨rfl, q, rfl, ht⟩ :
        args = [] ∧ ∃ q, rets = [q] ∧ ExpTables rd q ∧ ExpWinTab rd q := by
      match args, rets, hm with
      | [], [q], h => exact ⟨rfl, q, rfl, h⟩
    have hl := (expTabAll_iff rd q).1 ht
    refine ⟨setl (setv (setl (Val.ofArgs []) 0 [q]) 1 lit% expTabN fun t ↦ expTabWord t)
      2227 [q], rfl, fun t ht ↦ ?_, ?_, ?_⟩
    all_goals b1_look
    · exact ⟨by rw [Nat.add_sub_cancel], hl t ht⟩

end
end LeanVM.Guest.B1
