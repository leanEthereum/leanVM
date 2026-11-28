/-
  LeanVM.Guest.B1.Link.Suffixes

  B1 for `one_plus_suffixes` (41 specializations): the corners `Π_{k ≤ i < n} (1 + a_i)`.
-/

module

public import LeanVM.Guest.B1.Link.Forms
public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Guest.B1.Common.Find
import LeanVM.Guest.CoreRef

/-!
# `one_plus_suffixes`

`one_plus_suffixes(chain, a, n)` (G) stores `chain[n] = 1`, then from `k = n - 1` down to `0`
multiplies the running product by `1 + a[k]` and stores it at `chain[k]`; it returns `0`. Its
specialization `one_plus_suffixes__L{n}` is `opsBody n`: block `kk` (coordinate `n - 1 - kk`)
from value `4 kk + 2`, the first without the product (`opsBlk`). The stored words are
`belowE as k` (`Forms.lean`), the Statement's corners `prodE ((chi.drop h).map (1 + ·))`.
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Protocol.Verifier

@[expose] public section

/-- **`one_plus_suffixes(chain, a, n)`**: the `n` words `as` at `a`, and `chain[k] = belowE as k`
for `k ≤ n`; it returns `0`. -/
def MeaningOnePlusSuffixes (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [chain, a], rets => (∃ as : List E, as.length = n ∧ ReadsAt rd a as ∧
      ∀ k ≤ n, LoadHolds rd chain k (belowE as k)) ∧ rets = [0]
  | _, _ => False

/-- The specializations' names, `one_plus_suffixes__L{n}`, `n ≤ 40`. -/
def opsNames : List String := ["one_plus_suffixes__L0", "one_plus_suffixes__L1", "one_plus_suffixes__L2", "one_plus_suffixes__L3", "one_plus_suffixes__L4", "one_plus_suffixes__L5", "one_plus_suffixes__L6", "one_plus_suffixes__L7", "one_plus_suffixes__L8", "one_plus_suffixes__L9", "one_plus_suffixes__L10", "one_plus_suffixes__L11", "one_plus_suffixes__L12", "one_plus_suffixes__L13", "one_plus_suffixes__L14", "one_plus_suffixes__L15", "one_plus_suffixes__L16", "one_plus_suffixes__L17", "one_plus_suffixes__L18", "one_plus_suffixes__L19", "one_plus_suffixes__L20", "one_plus_suffixes__L21", "one_plus_suffixes__L22", "one_plus_suffixes__L23", "one_plus_suffixes__L24", "one_plus_suffixes__L25", "one_plus_suffixes__L26", "one_plus_suffixes__L27", "one_plus_suffixes__L28", "one_plus_suffixes__L29", "one_plus_suffixes__L30", "one_plus_suffixes__L31", "one_plus_suffixes__L32", "one_plus_suffixes__L33", "one_plus_suffixes__L34", "one_plus_suffixes__L35", "one_plus_suffixes__L36", "one_plus_suffixes__L37", "one_plus_suffixes__L38", "one_plus_suffixes__L39", "one_plus_suffixes__L40"]

/-- `one_plus_suffixes__L{n}`'s core IR implies its meaning, `n ≤ 40`. -/
def one_plus_suffixes_SoundP (P : Program) : Prop :=
  ∀ n ≤ 40, ∀ (rd : Reader) (args rets : List E),
    P.Rel rd (opsNames.getD n "") args rets → MeaningOnePlusSuffixes n rd args rets

/-! ## The template

The template is stated at a value offset `o` and the values `c` (`chain`) and `a`, so that a
caller inlining the same loop (`index_side`'s `below`) reads it too (`ops_run`). -/

/-- The value loaded from `a` in block `kk`. -/
def opsLd (o kk : ℕ) : ℕ := if kk = 0 then o + 4 else o + 4 * kk + 3

/-- The running product after block `kk`. -/
def opsV (o kk : ℕ) : ℕ := o + 4 * kk + 5

/-- Block `kk`: coordinate `n - 1 - kk`. -/
def opsBlk (o c a n kk : ℕ) : List Stmt :=
  if kk = 0 then
    [.atom (.const (.n (o + 3)) (word 1 0)), .atom (.load (.n (o + 4)) (.n a) (n - 1)),
      .atom (.add (.n (o + 5)) (.n (o + 3)) (.n (o + 4))), .atom (.load (.n (o + 5)) (.n c) (n - 1))]
  else
    [.atom (.const (.n (o + 4 * kk + 2)) (word 1 0)),
      .atom (.load (.n (o + 4 * kk + 3)) (.n a) (n - 1 - kk)),
      .atom (.add (.n (o + 4 * kk + 4)) (.n (o + 4 * kk + 2)) (.n (o + 4 * kk + 3))),
      .atom (.mul (.n (o + 4 * kk + 5)) (.n (opsV o (kk - 1))) (.n (o + 4 * kk + 4))),
      .atom (.load (.n (o + 4 * kk + 5)) (.n c) (n - 1 - kk))]

/-- The loop: `chain[n] = 1`, then the blocks. -/
def opsLoop (o c a n : ℕ) : List Stmt :=
  [.atom (.const (.n (o + 2)) (word 1 0)), .atom (.load (.n (o + 2)) (.n c) n)] ++
    ((List.range n).map (opsBlk o c a n)).flatten

/-- The returned value. -/
def opsEnd (n : ℕ) : ℕ := if n = 0 then 3 else 4 * n + 2

/-- The expansion of `one_plus_suffixes__L{n}`. -/
def opsBody (n : ℕ) : List Stmt :=
  opsLoop 0 0 1 n ++ [.atom (.const (.n (opsEnd n)) (word 0 0)), .ret [.n (opsEnd n)]]

/-- What block `kk` asks. -/
def OpsOk (rd : Reader) (σ : Val) (o c a n kk : ℕ) : Prop :=
  LoadHolds rd (σ (.n a)) (n - 1 - kk) (σ (.n (opsLd o kk))) ∧
    σ (.n (opsV o kk)) = (if kk = 0 then 1 else σ (.n (opsV o (kk - 1)))) *
      (1 + σ (.n (opsLd o kk))) ∧
    LoadHolds rd (σ (.n c)) (n - 1 - kk) (σ (.n (opsV o kk)))

theorem holds_opsBlk {C : CallRel} {rd : Reader} {σ : Val} (o c a n kk : ℕ)
    (kret : List E → Prop) (h : Stmt.HoldsList C rd σ (opsBlk o c a n kk) True kret) :
    OpsOk rd σ o c a n kk := by
  unfold opsBlk at h
  split_ifs at h with hk
  · subst hk
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one] at h
    obtain ⟨h3, l4, h5, l5⟩ := h
    refine ⟨by simpa [opsLd] using l4, ?_, by simpa [opsV] using l5⟩
    simp only [opsV, opsLd, ↓reduceIte]
    rw [h5, h3, one_mul]
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one] at h
    obtain ⟨h2, l3, h4, h5, l5⟩ := h
    refine ⟨by simpa [opsLd, hk] using l3, ?_, by simpa [opsV] using l5⟩
    simp only [opsV, opsLd, hk, ↓reduceIte] at h5 ⊢
    rw [h5, h4, h2]

theorem opsBlk_noRet (o c a n kk : ℕ) : Stmt.noRetList (opsBlk o c a n kk) = true := by
  unfold opsBlk; split <;> rfl

theorem belowE_eq_cons (as : List E) (k : ℕ) (hk : k < as.length) :
    belowE as k = (1 + as[k]) * belowE as (k + 1) := by
  rw [belowE, belowE, List.drop_eq_getElem_cons hk, List.map_cons, prodE_cons]

theorem belowE_length (as : List E) : belowE as as.length = 1 := by
  simp [belowE, prodE]

/-- **The loop's relation**: the `n` words at `a` and their suffix products at `chain`. -/
theorem ops_run {C : CallRel} {rd : Reader} {σ : Val} (o c a n : ℕ) {next : Prop}
    {kret : List E → Prop} (h : Stmt.HoldsList C rd σ (opsLoop o c a n) next kret) :
    (∃ as : List E, as.length = n ∧ ReadsAt rd (σ (.n a)) as ∧
      ∀ k ≤ n, LoadHolds rd (σ (.n c)) k (belowE as k)) ∧ next := by
  simp only [opsLoop, holdsList_append, holdsList_range_flatten n (opsBlk o c a n)
    (opsBlk_noRet o c a n), Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_one] at h
  obtain ⟨h2, l2, hblk, hnext⟩ := h
  refine ⟨?_, hnext⟩
  have hb := fun kk (hk : kk < n) ↦ holds_opsBlk (C := C) o c a n kk _ (hblk kk hk)
  -- the loaded words, by coordinate
  let as : List E := (List.range n).map fun k ↦ σ (.n (opsLd o (n - 1 - k)))
  have has : as.length = n := by simp [as]
  have hget : ∀ k (hk : k < as.length), as[k] = σ (.n (opsLd o (n - 1 - k))) := by
    intro k hk; simp [as]
  have hv : ∀ kk < n, σ (.n (opsV o kk)) = belowE as (n - 1 - kk) := by
    intro kk hkk
    induction kk with
    | zero =>
      obtain ⟨-, e, -⟩ := hb 0 hkk
      rw [e, belowE_eq_cons as _ (by omega), hget _ (by omega),
        show n - 1 - 0 + 1 = as.length by omega, belowE_length,
        show n - 1 - (n - 1 - 0) = 0 by omega]
      simp only [↓reduceIte, one_mul, mul_one]
    | succ kk ih =>
      obtain ⟨-, e, -⟩ := hb (kk + 1) hkk
      rw [e, Nat.add_sub_cancel, ih (by omega),
        belowE_eq_cons as (n - 1 - (kk + 1)) (by omega), hget _ (by omega),
        show n - 1 - (kk + 1) + 1 = n - 1 - kk by omega,
        show n - 1 - (n - 1 - (kk + 1)) = kk + 1 by omega]
      simp only [Nat.add_one_ne_zero, ↓reduceIte]
      ring
  refine ⟨as, has, fun k hk ↦ ?_, fun k hk ↦ ?_⟩
  · obtain ⟨l, -, -⟩ := hb (n - 1 - k) (by omega)
    rw [hget k hk]
    rwa [show n - 1 - (n - 1 - k) = k by omega] at l
  · rcases Nat.lt_or_ge k n with h | h
    · obtain ⟨-, -, l⟩ := hb (n - 1 - k) (by omega)
      rw [hv _ (by omega), show n - 1 - (n - 1 - k) = k by omega] at l
      exact l
    · obtain rfl : k = n := by omega
      rw [← has, belowE_length, has, ← h2]
      exact l2

/-- **The template's relation implies its meaning.** -/
theorem ops_sound (n : ℕ) {f : Fn} (hfind : coreProgram.find? (opsNames.getD n "") = some f)
    (hparams : f.params = [.n 0, .n 1]) (hbody : f.body = opsBody n) (rd : Reader)
    (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD n "") args rets → MeaningOnePlusSuffixes n rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams, opsBody]
  simp only [holdsList_append]
  rintro ⟨σ, rfl, h⟩
  obtain ⟨hm, h⟩ := ops_run 0 0 1 n h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_zero] at h
  obtain ⟨h0, hret⟩ := h
  exact ⟨hm, by rw [← hret, h0]⟩

/-! ## The specializations -/

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L0_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 0 "") args rets → MeaningOnePlusSuffixes 0 rd args rets :=
  ops_sound 0 (f := fn% «one_plus_suffixes__L0»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L0») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L1_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 1 "") args rets → MeaningOnePlusSuffixes 1 rd args rets :=
  ops_sound 1 (f := fn% «one_plus_suffixes__L1»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L1») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L2_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 2 "") args rets → MeaningOnePlusSuffixes 2 rd args rets :=
  ops_sound 2 (f := fn% «one_plus_suffixes__L2»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L2») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L3_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 3 "") args rets → MeaningOnePlusSuffixes 3 rd args rets :=
  ops_sound 3 (f := fn% «one_plus_suffixes__L3»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L3») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L4_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 4 "") args rets → MeaningOnePlusSuffixes 4 rd args rets :=
  ops_sound 4 (f := fn% «one_plus_suffixes__L4»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L4») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L5_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 5 "") args rets → MeaningOnePlusSuffixes 5 rd args rets :=
  ops_sound 5 (f := fn% «one_plus_suffixes__L5»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L5») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L6_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 6 "") args rets → MeaningOnePlusSuffixes 6 rd args rets :=
  ops_sound 6 (f := fn% «one_plus_suffixes__L6»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L6») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L7_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 7 "") args rets → MeaningOnePlusSuffixes 7 rd args rets :=
  ops_sound 7 (f := fn% «one_plus_suffixes__L7»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L7») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L8_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 8 "") args rets → MeaningOnePlusSuffixes 8 rd args rets :=
  ops_sound 8 (f := fn% «one_plus_suffixes__L8»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L8») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L9_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 9 "") args rets → MeaningOnePlusSuffixes 9 rd args rets :=
  ops_sound 9 (f := fn% «one_plus_suffixes__L9»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L9») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L10_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 10 "") args rets → MeaningOnePlusSuffixes 10 rd args rets :=
  ops_sound 10 (f := fn% «one_plus_suffixes__L10»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L10») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L11_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 11 "") args rets → MeaningOnePlusSuffixes 11 rd args rets :=
  ops_sound 11 (f := fn% «one_plus_suffixes__L11»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L11») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L12_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 12 "") args rets → MeaningOnePlusSuffixes 12 rd args rets :=
  ops_sound 12 (f := fn% «one_plus_suffixes__L12»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L12») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L13_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 13 "") args rets → MeaningOnePlusSuffixes 13 rd args rets :=
  ops_sound 13 (f := fn% «one_plus_suffixes__L13»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L13») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L14_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 14 "") args rets → MeaningOnePlusSuffixes 14 rd args rets :=
  ops_sound 14 (f := fn% «one_plus_suffixes__L14»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L14») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L15_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 15 "") args rets → MeaningOnePlusSuffixes 15 rd args rets :=
  ops_sound 15 (f := fn% «one_plus_suffixes__L15»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L15») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L16_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 16 "") args rets → MeaningOnePlusSuffixes 16 rd args rets :=
  ops_sound 16 (f := fn% «one_plus_suffixes__L16»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L16») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L17_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 17 "") args rets → MeaningOnePlusSuffixes 17 rd args rets :=
  ops_sound 17 (f := fn% «one_plus_suffixes__L17»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L17») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L18_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 18 "") args rets → MeaningOnePlusSuffixes 18 rd args rets :=
  ops_sound 18 (f := fn% «one_plus_suffixes__L18»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L18») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L19_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 19 "") args rets → MeaningOnePlusSuffixes 19 rd args rets :=
  ops_sound 19 (f := fn% «one_plus_suffixes__L19»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L19») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L20_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 20 "") args rets → MeaningOnePlusSuffixes 20 rd args rets :=
  ops_sound 20 (f := fn% «one_plus_suffixes__L20»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L20») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L21_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 21 "") args rets → MeaningOnePlusSuffixes 21 rd args rets :=
  ops_sound 21 (f := fn% «one_plus_suffixes__L21»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L21») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L22_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 22 "") args rets → MeaningOnePlusSuffixes 22 rd args rets :=
  ops_sound 22 (f := fn% «one_plus_suffixes__L22»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L22») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L23_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 23 "") args rets → MeaningOnePlusSuffixes 23 rd args rets :=
  ops_sound 23 (f := fn% «one_plus_suffixes__L23»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L23») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L24_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 24 "") args rets → MeaningOnePlusSuffixes 24 rd args rets :=
  ops_sound 24 (f := fn% «one_plus_suffixes__L24»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L24») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L25_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 25 "") args rets → MeaningOnePlusSuffixes 25 rd args rets :=
  ops_sound 25 (f := fn% «one_plus_suffixes__L25»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L25») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L26_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 26 "") args rets → MeaningOnePlusSuffixes 26 rd args rets :=
  ops_sound 26 (f := fn% «one_plus_suffixes__L26»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L26») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L27_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 27 "") args rets → MeaningOnePlusSuffixes 27 rd args rets :=
  ops_sound 27 (f := fn% «one_plus_suffixes__L27»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L27») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L28_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 28 "") args rets → MeaningOnePlusSuffixes 28 rd args rets :=
  ops_sound 28 (f := fn% «one_plus_suffixes__L28»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L28») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L29_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 29 "") args rets → MeaningOnePlusSuffixes 29 rd args rets :=
  ops_sound 29 (f := fn% «one_plus_suffixes__L29»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L29») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L30_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 30 "") args rets → MeaningOnePlusSuffixes 30 rd args rets :=
  ops_sound 30 (f := fn% «one_plus_suffixes__L30»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L30») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L31_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 31 "") args rets → MeaningOnePlusSuffixes 31 rd args rets :=
  ops_sound 31 (f := fn% «one_plus_suffixes__L31»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L31») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L32_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 32 "") args rets → MeaningOnePlusSuffixes 32 rd args rets :=
  ops_sound 32 (f := fn% «one_plus_suffixes__L32»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L32») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L33_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 33 "") args rets → MeaningOnePlusSuffixes 33 rd args rets :=
  ops_sound 33 (f := fn% «one_plus_suffixes__L33»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L33») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L34_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 34 "") args rets → MeaningOnePlusSuffixes 34 rd args rets :=
  ops_sound 34 (f := fn% «one_plus_suffixes__L34»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L34») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L35_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 35 "") args rets → MeaningOnePlusSuffixes 35 rd args rets :=
  ops_sound 35 (f := fn% «one_plus_suffixes__L35»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L35») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L36_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 36 "") args rets → MeaningOnePlusSuffixes 36 rd args rets :=
  ops_sound 36 (f := fn% «one_plus_suffixes__L36»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L36») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L37_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 37 "") args rets → MeaningOnePlusSuffixes 37 rd args rets :=
  ops_sound 37 (f := fn% «one_plus_suffixes__L37»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L37») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L38_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 38 "") args rets → MeaningOnePlusSuffixes 38 rd args rets :=
  ops_sound 38 (f := fn% «one_plus_suffixes__L38»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L38») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L39_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 39 "") args rets → MeaningOnePlusSuffixes 39 rd args rets :=
  ops_sound 39 (f := fn% «one_plus_suffixes__L39»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L39») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L40_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (opsNames.getD 40 "") args rets → MeaningOnePlusSuffixes 40 rd args rets :=
  ops_sound 40 (f := fn% «one_plus_suffixes__L40»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L40») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

/-- **`one_plus_suffixes`' core IR implies its meaning**, every specialization. -/
theorem one_plus_suffixes_sound : one_plus_suffixes_SoundP coreProgram := by
  intro n hn
  interval_cases n
  exacts [one_plus_suffixes_L0_sound, one_plus_suffixes_L1_sound, one_plus_suffixes_L2_sound, one_plus_suffixes_L3_sound, one_plus_suffixes_L4_sound, one_plus_suffixes_L5_sound, one_plus_suffixes_L6_sound, one_plus_suffixes_L7_sound, one_plus_suffixes_L8_sound, one_plus_suffixes_L9_sound, one_plus_suffixes_L10_sound, one_plus_suffixes_L11_sound, one_plus_suffixes_L12_sound, one_plus_suffixes_L13_sound, one_plus_suffixes_L14_sound, one_plus_suffixes_L15_sound, one_plus_suffixes_L16_sound, one_plus_suffixes_L17_sound, one_plus_suffixes_L18_sound, one_plus_suffixes_L19_sound, one_plus_suffixes_L20_sound, one_plus_suffixes_L21_sound, one_plus_suffixes_L22_sound, one_plus_suffixes_L23_sound, one_plus_suffixes_L24_sound, one_plus_suffixes_L25_sound, one_plus_suffixes_L26_sound, one_plus_suffixes_L27_sound, one_plus_suffixes_L28_sound, one_plus_suffixes_L29_sound, one_plus_suffixes_L30_sound, one_plus_suffixes_L31_sound, one_plus_suffixes_L32_sound, one_plus_suffixes_L33_sound, one_plus_suffixes_L34_sound, one_plus_suffixes_L35_sound, one_plus_suffixes_L36_sound, one_plus_suffixes_L37_sound, one_plus_suffixes_L38_sound, one_plus_suffixes_L39_sound, one_plus_suffixes_L40_sound]

end
end LeanVM.Guest.B1.Link
