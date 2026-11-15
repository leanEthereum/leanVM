/-
  LeanVM.Guest.B1.Digest.Chain

  A checker, by kernel evaluation, that a straight-line list of atoms holds a `KECCAK` chain over
  message cells (`keccak` and `keccak_cells`, as `emit_keccak_message` lowers them), and its
  soundness: the chain's last output is Keccak-256 of the cells' bytes (or, with `final=0`, the
  sponge state after them).
-/

module

public import LeanVM.Guest.B1.Digest.Basic

/-!
# `KECCAK` chains, checked by evaluation

The compiler lowers `keccak(...)` and `keccak_cells(...)` (`emit_keccak_message`,
`crates/lean_compiler/src/lower/builtins.rs` at leanVM `40f877dc`) to one `KECCAK` per block
of `136` bytes: block `k` reads nine message cells from cell `17k/2` XORed into the previous output
(or the zero state, or a `state=` run), its four capacity cells the previous output's, and the
padding bytes `0x01`, `0x80` XORed in as constants (folded into a `Zero` cell, or one `XOR` with a
constant cell; with `pad_tail=1` the `0x01` is instead `SET` into the tail's cell beforehand,
`pad_tail_in_place`, `builtins.rs`). The value names vary with the caller; the shape does
not.

A `ChainSpec` names the message cells (`some v`, a value, or `none`, a zero cell), the length in
bytes, whether the chain pads (`final`), its initial state (`none`: the zero state; `some st`:
thirteen values, a `state=` run) and its blocks' input and output values. `check atoms s` is a
Boolean that the kernel evaluates (`decide +kernel`): every block is a `KECCAK` atom of the list
in the layouts `inLayout k`, `outLayout B k`, and every input cell is, by an atom of the list,
the previous output's cell plus the padded message cell (`rateOk`), or the previous output's
capacity cell (`capOk`). It is sound for every valuation satisfying the atoms:

* `chain_final` (`final`): the last output's cells `0`, `1` are the digest of `pre ++` the
  message's bytes, after a prefix `pre` of whole blocks absorbed into the initial state;
* `chain_whole` (`final=0`): the last output is the sponge state after `pre ++` the cells' bytes.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

open scoped VDec

@[expose] public section

/-! ## Atom matchers -/

/-- `x` is set to the word `word lo hi`. -/
def isConstAt (x : V) (lo hi : ℕ) : Atom → Bool
  | .const d c => decide (d = x) && eEqb c (word lo hi)
  | _ => false

/-- `x = y + z`. -/
def isAddAt (x y z : V) : Atom → Bool
  | .add d a b => decide (d = x) && decide (a = y) && decide (b = z)
  | _ => false

/-- `x = y`. -/
def isCopyAt (x y : V) : Atom → Bool
  | .copy d s => decide (d = x) && decide (s = y)
  | _ => false

/-- The `KECCAK` of these cells and layouts. -/
def isKeccakAt (ins outs : List V) (i o : Bool) : Atom → Bool
  | .keccak a b c d => decide (a = ins) && decide (b = outs) && decide (c = i) && decide (d = o)
  | _ => false

/-- The operands of the first `XOR` into `x`. -/
def addOf (atoms : List Atom) (x : V) : Option (V × V) :=
  atoms.findSome? fun a => match a with
    | .add d p q => if d = x then some (p, q) else none
    | _ => none

variable {rd : Reader} {σ : Val}

theorem any_holds {atoms : List Atom} {p : Atom → Bool} (h : atoms.any p = true)
    (hat : ∀ a ∈ atoms, a.Holds rd σ) : ∃ a, p a = true ∧ a.Holds rd σ := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  exact ⟨a, hp, hat a ha⟩

theorem const_sound {atoms : List Atom} {x : V} {lo hi : ℕ}
    (h : atoms.any (isConstAt x lo hi) = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    σ x = word lo hi := by
  obtain ⟨a, hp, ha⟩ := any_holds h hat
  cases a <;> simp only [isConstAt, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨rfl, he⟩ := hp
  rw [← eEqb_sound he]
  exact ha

theorem add_sound {atoms : List Atom} {x y z : V} (h : atoms.any (isAddAt x y z) = true)
    (hat : ∀ a ∈ atoms, a.Holds rd σ) : σ x = σ y + σ z := by
  obtain ⟨a, hp, ha⟩ := any_holds h hat
  cases a <;> simp only [isAddAt, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hp
  exact ha

theorem copy_sound {atoms : List Atom} {x y : V} (h : atoms.any (isCopyAt x y) = true)
    (hat : ∀ a ∈ atoms, a.Holds rd σ) : σ x = σ y := by
  obtain ⟨a, hp, ha⟩ := any_holds h hat
  cases a <;> simp only [isCopyAt, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  exact ha

theorem keccak_sound {atoms : List Atom} {ins outs : List V} {i o : Bool}
    (h : atoms.any (isKeccakAt ins outs i o) = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    (Atom.keccak ins outs i o).Holds rd σ := by
  obtain ⟨a, hp, ha⟩ := any_holds h hat
  cases a <;> simp only [isKeccakAt, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hp
  exact ha

theorem addOf_sound {atoms : List Atom} {x p q : V} (h : addOf atoms x = some (p, q))
    (hat : ∀ a ∈ atoms, a.Holds rd σ) : σ x = σ p + σ q := by
  obtain ⟨a, ha, hs⟩ := List.exists_of_findSome?_eq_some h
  have := hat a ha
  cases a <;> simp only [reduceCtorEq] at hs
  rename_i d p' q'
  split at hs
  · rename_i hd
    obtain ⟨rfl, rfl⟩ := Option.some.inj hs
    subst hd
    exact this
  · exact absurd hs (by simp)

/-! ## The padded message cell -/

/-- A message cell's value: the value, or zero. -/
def srcVal (σ : Val) : Option V → E
  | some v => σ v
  | none => 0

/-- Some `XOR` into `x` of operands passing `f`: a membership test, so a check of a sublist is a
check of the list (`addWith_sub`). -/
def addWith (atoms : List Atom) (x : V) (f : V → V → Bool) : Bool :=
  atoms.any fun a => match a with
    | .add d p q => decide (d = x) && f p q
    | _ => false

theorem addWith_sound {atoms : List Atom} {x : V} {f : V → V → Bool} (h : addWith atoms x f = true)
    (hat : ∀ a ∈ atoms, a.Holds rd σ) : ∃ p q, f p q = true ∧ σ x = σ p + σ q := by
  obtain ⟨a, hp, ha⟩ := any_holds h hat
  cases a <;> simp only [Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨rfl, hf⟩ := hp
  exact ⟨_, _, hf, ha⟩

/-- **`x` is the message cell `src` plus the padding constant** `word lo hi`. -/
def evalP (atoms : List Atom) (x : V) (src : Option V) (lo hi : ℕ) : Bool :=
  match src with
  | some v => (lo == 0 && hi == 0 && decide (x = v)) ||
      addWith atoms x fun p q => (decide (p = v) && atoms.any (isConstAt q lo hi)) ||
        (decide (q = v) && atoms.any (isConstAt p lo hi))
  | none => atoms.any (isConstAt x lo hi)

theorem evalP_sound {atoms : List Atom} {x : V} {src : Option V} {lo hi : ℕ}
    (h : evalP atoms x src lo hi = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    σ x = srcVal σ src + word lo hi := by
  cases src with
  | none =>
    simp only [evalP] at h
    rw [const_sound h hat, srcVal, zero_add]
  | some v =>
    simp only [evalP, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    rcases h with ⟨⟨rfl, rfl⟩, rfl⟩ | h
    · rw [srcVal, word_zero, add_zero]
    · obtain ⟨p, q, h, hx⟩ := addWith_sound h hat
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨rfl, hc⟩ | ⟨rfl, hc⟩
      · rw [hx, const_sound hc hat, srcVal]
      · rw [hx, const_sound hc hat, srcVal, add_comm]

/-- **The rate cell `x` is the previous output's cell `y` (`none`: zero) plus the padded
message cell.** -/
def rateOk (atoms : List Atom) (x : V) (y : Option V) (src : Option V) (lo hi : ℕ) : Bool :=
  match y with
  | none => evalP atoms x src lo hi
  | some y =>
    (src.isNone && lo == 0 && hi == 0 && (decide (x = y) || atoms.any (isCopyAt x y))) ||
    addWith atoms x fun p q => (decide (p = y) && evalP atoms q src lo hi) ||
      (decide (q = y) && evalP atoms p src lo hi)

theorem rateOk_sound {atoms : List Atom} {x : V} {y src : Option V} {lo hi : ℕ}
    (h : rateOk atoms x y src lo hi = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    σ x = srcVal σ y + (srcVal σ src + word lo hi) := by
  cases y with
  | none =>
    simp only [rateOk] at h
    rw [evalP_sound h hat, srcVal, zero_add]
  | some y =>
    simp only [rateOk, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      Option.isNone_iff_eq_none] at h
    rcases h with ⟨⟨⟨rfl, rfl⟩, rfl⟩, h⟩ | h
    · rw [srcVal, srcVal, word_zero, add_zero, add_zero]
      rcases h with rfl | h
      · rfl
      · exact copy_sound h hat
    · obtain ⟨p, q, h, hx⟩ := addWith_sound h hat
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨rfl, he⟩ | ⟨rfl, he⟩
      · rw [hx, evalP_sound he hat, srcVal]
      · rw [hx, evalP_sound he hat, srcVal, add_comm]

/-! ## Checks of a sublist

Every check above is a membership test, so it holds of a list when it holds of a sublist: a window
of the checks searches a slice of the atoms. -/

theorem any_sub {l l' : List Atom} (hs : ∀ a ∈ l, a ∈ l') {p : Atom → Bool} (h : l.any p = true) :
    l'.any p = true := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨a, hs a ha, hp⟩

theorem addWith_sub {l l' : List Atom} (hs : ∀ a ∈ l, a ∈ l') {x : V} {f f' : V → V → Bool}
    (hf : ∀ p q, f p q = true → f' p q = true) (h : addWith l x f = true) :
    addWith l' x f' = true := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  refine List.any_eq_true.mpr ⟨a, hs a ha, ?_⟩
  cases a <;> simp only [Bool.false_eq_true, Bool.and_eq_true] at hp ⊢
  exact ⟨hp.1, hf _ _ hp.2⟩

theorem evalP_sub {l l' : List Atom} (hs : ∀ a ∈ l, a ∈ l') {x : V} {src : Option V} {lo hi : ℕ}
    (h : evalP l x src lo hi = true) : evalP l' x src lo hi = true := by
  cases src with
  | none => exact any_sub hs h
  | some v =>
    simp only [evalP, Bool.or_eq_true] at h ⊢
    refine h.imp id (addWith_sub hs fun p q hpq => ?_)
    simp only [Bool.or_eq_true, Bool.and_eq_true] at hpq ⊢
    exact hpq.imp (fun h => ⟨h.1, any_sub hs h.2⟩) (fun h => ⟨h.1, any_sub hs h.2⟩)

theorem rateOk_sub {l l' : List Atom} (hs : ∀ a ∈ l, a ∈ l') {x : V} {y src : Option V}
    {lo hi : ℕ} (h : rateOk l x y src lo hi = true) : rateOk l' x y src lo hi = true := by
  cases y with
  | none => exact evalP_sub hs h
  | some y =>
    simp only [rateOk, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
    refine h.imp (fun h => ⟨h.1, h.2.imp id (any_sub hs)⟩) (addWith_sub hs fun p q hpq => ?_)
    simp only [Bool.or_eq_true, Bool.and_eq_true] at hpq ⊢
    exact hpq.imp (fun h => ⟨h.1, evalP_sub hs h.2⟩) (fun h => ⟨h.1, evalP_sub hs h.2⟩)

/-! ## The padding constants -/

/-- Byte `v` at byte `pos` of the message, as the limbs of cell `i` (`byteCell`, zero elsewhere). -/
def byteNat (pos v i : ℕ) : ℕ × ℕ :=
  if pos / 16 = i then
    (if pos % 16 < 8 then (v * 2 ^ (8 * (pos % 16)), 0) else (0, v * 2 ^ (8 * (pos % 16 - 8))))
  else (0, 0)

/-- The padding of a message of `len` bytes in cell `i`: `0x01` at `len`, `0x80` at the last
block's last byte. -/
def padNat (len i : ℕ) : ℕ × ℕ :=
  let a := byteNat len 1 i
  let b := byteNat (rate * (len / rate + 1) - 1) 0x80 i
  (a.1 ^^^ b.1, a.2 ^^^ b.2)

theorem word_xor (a b c d : ℕ) : word (a ^^^ c) (b ^^^ d) = word a b + word c d := by
  simp only [word, ofBits_xor, ofLimbs_add]

theorem word_byteNat (pos v i : ℕ) :
    word (byteNat pos v i).1 (byteNat pos v i).2 = if i = pos / 16 then byteCell pos v else 0 := by
  unfold byteNat byteCell
  by_cases h : pos / 16 = i
  · rw [ite_pos' h, ite_pos' h.symm]
    split <;> rfl
  · rw [ite_neg' h, ite_neg' (Ne.symm h), word_zero]

theorem word_padNat (len i : ℕ) :
    word (padNat len i).1 (padNat len i).2 =
      (if i = len / 16 then byteCell len 1 else 0) +
        (if i = (rate * (len / rate + 1) - 1) / 16 then byteCell (rate * (len / rate + 1) - 1) 0x80
          else 0) := by
  rw [padNat, word_xor, word_byteNat, word_byteNat]

theorem getD_modify' {α : Type} (l : List α) (f : α → α) (j i : ℕ) (d : α) (hi : i < l.length) :
    (l.modify j f).getD i d = if j = i then f (l.getD i d) else l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_modify, List.getElem?_eq_getElem hi,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  split <;> rfl

/-- Cell `i` of the padded cells: the cell, plus the padding bytes it holds. -/
theorem padCells_getD (cells : List E) (len : ℕ) {i : ℕ} (hi : i < padRead len) :
    (padCells cells len).getD i 0 = cells.getD i 0 + word (padNat len i).1 (padNat len i).2 := by
  rw [word_padNat]
  have hlen : i < (cells ++ List.replicate (padRead len - cells.length) 0).length := by
    rw [List.length_append, List.length_replicate]; omega
  have hbase : (cells ++ List.replicate (padRead len - cells.length) 0).getD i 0 = cells.getD i 0 := by
    rcases Nat.lt_or_ge i cells.length with h | h
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, List.getD_eq_getElem?_getD]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h, List.getElem?_replicate,
        ite_pos' (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  unfold padCells xorByte
  rw [getD_modify' _ _ _ _ _ (by rw [List.length_modify]; exact hlen), getD_modify' _ _ _ _ _ hlen,
    hbase]
  by_cases h1 : len / 16 = i <;> by_cases h2 : (rate * (len / rate + 1) - 1) / 16 = i
  · rw [ite_pos' h2, ite_pos' h1, ite_pos' h1.symm, ite_pos' h2.symm, add_assoc]
  · rw [ite_neg' h2, ite_pos' h1, ite_pos' h1.symm, ite_neg' (Ne.symm h2), add_zero]
  · rw [ite_pos' h2, ite_neg' h1, ite_neg' (Ne.symm h1), ite_pos' h2.symm, zero_add]
  · rw [ite_neg' h2, ite_neg' h1, ite_neg' (Ne.symm h1), ite_neg' (Ne.symm h2), add_zero,
      add_zero]

/-! ## The checker -/

/-- A `KECCAK` chain over message cells. -/
structure ChainSpec where
  /-- The message cells: a value, or a zero cell. -/
  msg : List (Option V)
  /-- The message's length in bytes (`final`). -/
  len : ℕ
  /-- Whether the chain pads (`final`, the default). -/
  final : Bool
  /-- The initial state: the zero state, or thirteen values (`state=`). -/
  init : Option (List V)
  /-- Each block's thirteen input values and its output values: thirteen, or the last block of a
  padded chain two. -/
  blocks : List (List V × List V)

namespace ChainSpec

variable (s : ChainSpec)

/-- The number of blocks. -/
def nb : ℕ := s.blocks.length

/-- Input value `c` of block `k`. -/
def inV (k c : ℕ) : V := (s.blocks.getD k ([], [])).1.getD c default

/-- Output value `c` of block `k`. -/
def outV (k c : ℕ) : V := (s.blocks.getD k ([], [])).2.getD c default

/-- The previous output's value `c` before block `k` (`none`: the zero state). -/
def prevV (k c : ℕ) : Option V :=
  if k = 0 then s.init.map fun st => st.getD c default else some (s.outV (k - 1) c)

/-- The padding of message cell `i`. -/
def pad (i : ℕ) : ℕ × ℕ := if s.final then padNat s.len i else (0, 0)

/-- Block `k` is a `KECCAK` of the list in its layouts, writing the thirteen cells of the state,
or, the last block of a padded chain, the digest's two (`keccak_out`'s `out_cells`). -/
def blockOk (atoms : List Atom) (k : ℕ) : Bool :=
  (s.blocks.getD k ([], [])).1.length == 13 &&
    ((s.blocks.getD k ([], [])).2.length == 13 ||
      (s.final && k + 1 == s.nb && (s.blocks.getD k ([], [])).2.length == 2)) &&
    atoms.any (isKeccakAt (s.blocks.getD k ([], [])).1 (s.blocks.getD k ([], [])).2 (inLayout k)
      (outLayout s.nb k))

/-- Rate cell `c < 9` of block `k`. -/
def rateAt (atoms : List Atom) (k c : ℕ) : Bool :=
  rateOk atoms (s.inV k c) (s.prevV k c) (s.msg.getD (17 * k / 2 + c) none)
    (s.pad (17 * k / 2 + c)).1 (s.pad (17 * k / 2 + c)).2

/-- Capacity cell `c ≥ 9` of block `k`. -/
def capAt (atoms : List Atom) (k c : ℕ) : Bool :=
  match s.prevV k c with
  | none => atoms.any (isConstAt (s.inV k c) 0 0)
  | some y => decide (s.inV k c = y)

/-- The shape: a padded chain's block count and whole-cell length, or whole blocks. -/
def shapeOk : Bool :=
  (match s.init with | none => true | some st => st.length == 13) &&
  if s.final then
    s.nb == s.len / rate + 1 && s.len % 16 == 0 && decide (s.len ≤ 16 * s.msg.length) &&
      (s.msg.drop (s.len / 16)).all Option.isNone
  else 16 * s.msg.length == rate * s.nb && decide (0 < s.nb)

/-- **The checker.** -/
def check (atoms : List Atom) : Bool :=
  s.shapeOk && (List.range s.nb).all fun k =>
    s.blockOk atoms k && (List.range 9).all (s.rateAt atoms k) &&
      (List.range 4).all fun j => s.capAt atoms k (9 + j)

theorem blockOk_sub {l l' : List Atom} (hs : ∀ a ∈ l, a ∈ l') {k : ℕ} (h : s.blockOk l k = true) :
    s.blockOk l' k = true := by
  simp only [blockOk, Bool.and_eq_true] at h ⊢
  exact ⟨h.1, any_sub hs h.2⟩

theorem rateAt_sub {l l' : List Atom} (hs : ∀ a ∈ l, a ∈ l') {k c : ℕ} (h : s.rateAt l k c = true) :
    s.rateAt l' k c = true :=
  rateOk_sub hs h

theorem capAt_sub {l l' : List Atom} (hs : ∀ a ∈ l, a ∈ l') {k c : ℕ} (h : s.capAt l k c = true) :
    s.capAt l' k c = true := by
  unfold capAt at h ⊢
  split at h
  · exact any_sub hs h
  · exact h

/-- The message's values. -/
def vals (σ : Val) : List E := s.msg.map (srcVal σ)

/-- The initial state's cells. -/
def initCell (σ : Val) (c : ℕ) : E :=
  match s.init with
  | none => 0
  | some st => σ (st.getD c default)

end ChainSpec

/-! ## Soundness -/

theorem cells13_map (σ : Val) (vs : List V) (hl : vs.length = 13) (c : Fin 13) :
    cells13 (vs.map σ) c = σ (vs.getD c default) := by
  simp [cells13, List.getD_eq_getElem?_getD, show c.val < vs.length by omega]

theorem cellByte_zero (b : ℕ) : cellByte 0 b = 0 := by
  unfold cellByte
  rw [limb_zero, kBytes_zero, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem cellsBytes_take (cs : List E) (m : ℕ) :
    (cellsBytes cs).take (16 * m) = cellsBytes (cs.take m) := by
  induction cs generalizing m with
  | nil => simp
  | cons c cs ih =>
    cases m with
    | zero => simp
    | succ m =>
      rw [cellsBytes_cons, List.take_succ_cons, cellsBytes_cons,
        show 16 * (m + 1) = (cellBytes c).length + 16 * m by rw [length_cellBytes]; ring,
        List.take_length_add_append, ih]

namespace ChainSpec

variable {s : ChainSpec} {atoms : List Atom}

/-- The inputs and outputs of the chain, as `keccak_chain` reads them. -/
def I (s : ChainSpec) (σ : Val) (k : ℕ) (c : Fin 13) : E := σ (s.inV k c)

/-- The state before block `k`: the initial state's cells, then block `k - 1`'s Keccak-f, whose
first cells its written values are (`out_of_check`). -/
def O (s : ChainSpec) (σ : Val) (k : ℕ) (c : Fin 13) : E :=
  if k = 0 then s.initCell σ c
  else cellsOfState (keccakF1600 (stateOfCells (s.I σ (k - 1)) (inLayout (k - 1))))
    (outLayout s.nb (k - 1)) c

theorem check_parts (h : s.check atoms = true) :
    s.shapeOk = true ∧ ∀ k < s.nb, s.blockOk atoms k = true ∧
      (∀ c < 9, s.rateAt atoms k c = true) ∧ ∀ j < 4, s.capAt atoms k (9 + j) = true := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1, fun k hk => ⟨(h.2 k hk).1.1, (h.2 k hk).1.2, (h.2 k hk).2⟩⟩

theorem keccak_of_check (h : s.check atoms = true) (hat : ∀ a ∈ atoms, a.Holds rd σ)
    {k : ℕ} (hk : k < s.nb) :
    KeccakCellsRelation (s.I σ k) (inLayout k) (s.O σ (k + 1)) (outLayout s.nb k) .all := by
  obtain ⟨-, hb⟩ := check_parts h
  obtain ⟨hbk, -, -⟩ := hb k hk
  simp only [blockOk, Bool.and_eq_true, beq_iff_eq] at hbk
  obtain ⟨⟨h1, -⟩, hk'⟩ := hbk
  obtain ⟨-, -, O', hK, -⟩ := keccak_holds_full (keccak_sound hk' hat)
  have e1 : cells13 ((s.blocks.getD k ([], [])).1.map σ) = s.I σ k := funext (cells13_map σ _ h1)
  rw [e1] at hK
  exact fun c _ => by simp [O]

/-- Block `k`'s written values are the first cells of the state after it. -/
theorem out_of_check (h : s.check atoms = true) (hat : ∀ a ∈ atoms, a.Holds rd σ)
    {k : ℕ} (hk : k < s.nb) (c : Fin 13) (hc : c.val < (s.blocks.getD k ([], [])).2.length) :
    σ (s.outV k c) = s.O σ (k + 1) c := by
  obtain ⟨-, hb⟩ := check_parts h
  obtain ⟨hbk, -, -⟩ := hb k hk
  simp only [blockOk, Bool.and_eq_true, beq_iff_eq] at hbk
  obtain ⟨⟨h1, -⟩, hk'⟩ := hbk
  obtain ⟨-, -, O', hK, hw⟩ := keccak_holds_full (keccak_sound hk' hat)
  have e1 : cells13 ((s.blocks.getD k ([], [])).1.map σ) = s.I σ k := funext (cells13_map σ _ h1)
  rw [e1] at hK
  rw [outV, List.getD_eq_getElem _ _ hc, hw c hc, hK c c.isLt]
  simp [O]

/-- A block before the last writes the thirteen cells of the state. -/
theorem outs_13 (h : s.check atoms = true) {k : ℕ} (hk : k + 1 < s.nb) :
    (s.blocks.getD k ([], [])).2.length = 13 := by
  obtain ⟨-, hb⟩ := check_parts h
  obtain ⟨hbk, -, -⟩ := hb k (by omega)
  simp only [blockOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hbk
  rcases hbk.1.2 with h13 | ⟨⟨-, hl⟩, -⟩
  · exact h13
  · omega

/-- The last block writes at least the digest's two cells. -/
theorem outs_last_two (h : s.check atoms = true) (hnb : 0 < s.nb) :
    2 ≤ (s.blocks.getD (s.nb - 1) ([], [])).2.length := by
  obtain ⟨-, hb⟩ := check_parts h
  obtain ⟨hbk, -, -⟩ := hb (s.nb - 1) (by omega)
  simp only [blockOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hbk
  rcases hbk.1.2 with h13 | ⟨-, hl⟩ <;> omega

/-- Every block of a chain without padding writes the thirteen cells of the state. -/
theorem outs_whole (h : s.check atoms = true) (hfin : s.final = false) {k : ℕ} (hk : k < s.nb) :
    (s.blocks.getD k ([], [])).2.length = 13 := by
  obtain ⟨-, hb⟩ := check_parts h
  obtain ⟨hbk, -, -⟩ := hb k hk
  simp only [blockOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, hfin] at hbk
  rcases hbk.1.2 with h13 | ⟨⟨h', -⟩, -⟩
  · exact h13
  · exact absurd h' (by decide)

theorem prevV_val (h : s.check atoms = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) {k : ℕ}
    (hk : k < s.nb) (c : ℕ) (hc : c < 13) :
    srcVal σ (s.prevV k c) = s.O σ k ⟨c, hc⟩ := by
  by_cases hk0 : k = 0
  · unfold prevV O initCell
    rw [ite_pos' hk0, ite_pos' hk0]
    cases s.init <;> rfl
  · unfold prevV
    rw [ite_neg' hk0, srcVal]
    have := out_of_check h hat (k := k - 1) (by omega) ⟨c, hc⟩
      (by rw [outs_13 h (by omega)]; exact hc)
    rwa [Nat.sub_add_cancel (by omega)] at this

/-- The rate relation, for any padded cells `P` that hold the message cells plus `pad`. -/
theorem rate_of_check (h : s.check atoms = true) (hat : ∀ a ∈ atoms, a.Holds rd σ)
    {k : ℕ} (hk : k < s.nb) (c : Fin 13) (hc : c.val < 9) :
    s.I σ k c = s.O σ k c + (srcVal σ (s.msg.getD (17 * k / 2 + c) none) +
      word (s.pad (17 * k / 2 + c)).1 (s.pad (17 * k / 2 + c)).2) := by
  obtain ⟨hs, hb⟩ := check_parts h
  obtain ⟨-, hr, -⟩ := hb k hk
  have := rateOk_sound (hr c hc) hat
  rw [prevV_val h hat hk c c.isLt] at this
  exact this

theorem cap_of_check (h : s.check atoms = true) (hat : ∀ a ∈ atoms, a.Holds rd σ)
    {k : ℕ} (hk : k < s.nb) (c : Fin 13) (hc : 9 ≤ c.val) : s.I σ k c = s.O σ k c := by
  obtain ⟨hs, hb⟩ := check_parts h
  obtain ⟨-, -, hcap⟩ := hb k hk
  have hc' := hcap (c.val - 9) (by omega)
  rw [show 9 + (c.val - 9) = c.val by omega] at hc'
  have hv := prevV_val h hat hk c c.isLt
  unfold capAt at hc'
  unfold I
  rw [← hv]
  split at hc'
  · rename_i hp
    rw [hp, srcVal, const_sound hc' hat, word_zero]
  · rename_i y hp
    rw [hp, srcVal, of_decide_eq_true hc']

theorem srcVal_getD (σ : Val) (msg : List (Option V)) (i : ℕ) :
    srcVal σ (msg.getD i none) = (msg.map (srcVal σ)).getD i 0 := by
  rcases Nat.lt_or_ge i msg.length with h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, srcVal]

end ChainSpec

open ChainSpec in
/-- **A padded chain computes Keccak-256** of `pre ++` its message's bytes, `pre` the whole blocks
absorbed into the initial state. -/
theorem chain_final {s : ChainSpec} {atoms : List Atom} (h : s.check atoms = true)
    (hfin : s.final = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) {pre : List UInt8} {n : ℕ}
    (hpre : pre.length = rate * n)
    (h0 : ∀ c : Fin 13, s.initCell σ c = cellsOfState (absorbChunks n zeroState pre) false c) :
    (σ (s.outV (s.nb - 1) 0), σ (s.outV (s.nb - 1) 1)) =
        digestHalves (keccak256 (pre ++ cellsBytes ((s.vals σ).take (s.len / 16)))) := by
  obtain ⟨hs, -⟩ := check_parts h
  have hs' := hs
  simp only [shapeOk, hfin, ↓reduceIte, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true] at hs'
  have hnb := hs'.2.1.1.1
  have hmod := hs'.2.1.1.2
  have hle := hs'.2.1.2
  have hzero := hs'.2.2
  have hvl : (s.vals σ).length = s.msg.length := by simp [vals]
  have hpad : ∀ i, s.pad i = padNat s.len i := fun i => by simp [pad, hfin]
  have hrate : ∀ k < s.len / rate + 1, ∀ c : Fin 13, c.val < 9 →
      s.I σ k c = s.O σ k c + (padCells (s.vals σ) s.len).getD (17 * k / 2 + c) 0 := by
    intro k hk c hc
    rw [← hnb] at hk
    rw [rate_of_check h hat hk c hc, padCells_getD _ _ (by unfold padRead; rw [hnb] at hk; omega),
      hpad, srcVal_getD]
    rfl
  have hcap : ∀ k < s.len / rate + 1, ∀ c : Fin 13, 9 ≤ c.val → s.I σ k c = s.O σ k c :=
    fun k hk c hc => cap_of_check h hat (by rw [hnb]; exact hk) c hc
  have hK : ∀ k < s.len / rate + 1,
      KeccakCellsRelation (s.I σ k) (inLayout k) (s.O σ (k + 1)) (outLayout (s.len / rate + 1) k)
        .all :=
    fun k hk => by rw [← hnb]; exact keccak_of_check h hat (by rw [hnb]; exact hk)
  have hz : ∀ j, s.len ≤ j → (cellsBytes (s.vals σ)).getD j 0 = 0 := by
    intro j hj
    rw [getD_cellsBytes]
    rcases Nat.lt_or_ge (j / 16) s.msg.length with hl | hl
    · have hn := hzero (s.msg[j / 16]) (List.mem_iff_getElem.mpr ⟨j / 16 - s.len / 16,
        by rw [List.length_drop]; omega, by rw [List.getElem_drop]; congr 1; omega⟩)
      rw [Option.isNone_iff_eq_none] at hn
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hvl]; exact hl)]
      simp only [vals, List.getElem_map, hn, srcVal, Option.getD_some, cellByte_zero]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hvl]; exact hl)]
      exact cellByte_zero _
  have hO0 : s.O σ 0 = cellsOfState (absorbChunks n zeroState pre) false := by
    funext c; simp only [O, ↓reduceIte]; exact h0 c
  have hlen : s.len ≤ 16 * (s.vals σ).length := by rw [hvl]; exact hle
  have hdig := keccak_final_digest hpre hlen hz hO0 hrate hcap hK
  have hout : ∀ c : Fin 13, c.val < 2 → s.O σ (s.len / rate + 1) c = σ (s.outV (s.nb - 1) c) :=
    fun c hc => by
      have hpos : 0 < s.nb := by rw [hnb]; exact Nat.succ_pos _
      have hk1 : s.nb - 1 < s.nb := by omega
      have h2 := outs_last_two h hpos
      have := out_of_check h hat hk1 c (by omega)
      rw [Nat.sub_add_cancel hpos] at this
      rw [← hnb, this]
  rw [hout 0 (by decide), hout 1 (by decide)] at hdig
  have hm : s.len = 16 * (s.len / 16) := by omega
  show (σ (s.outV (s.nb - 1) ((0 : Fin 13) : ℕ)), σ (s.outV (s.nb - 1) ((1 : Fin 13) : ℕ))) = _
  rw [hdig, ← cellsBytes_take, ← hm]

open ChainSpec in
/-- **A chain of whole blocks without padding** (`final=0`) leaves the sponge state after
`pre ++` its cells' bytes. -/
theorem chain_whole {s : ChainSpec} {atoms : List Atom} (h : s.check atoms = true)
    (hfin : s.final = false) (hat : ∀ a ∈ atoms, a.Holds rd σ) {pre : List UInt8} {n : ℕ}
    (hpre : pre.length = rate * n)
    (h0 : ∀ c : Fin 13, s.initCell σ c = cellsOfState (absorbChunks n zeroState pre) false c) :
    (∀ c : Fin 13, σ (s.outV (s.nb - 1) c) =
        cellsOfState (absorbChunks (n + s.nb) zeroState (pre ++ cellsBytes (s.vals σ))) false c) ∧
      (pre ++ cellsBytes (s.vals σ)).length = rate * (n + s.nb) := by
  obtain ⟨hs, -⟩ := check_parts h
  have hs' := hs
  simp only [shapeOk, hfin, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hs'
  have hB := hs'.2.1
  have hpos := hs'.2.2
  have hvl : (s.vals σ).length = s.msg.length := by simp [vals]
  have hpad : ∀ i, s.pad i = (0, 0) := fun i => by simp [pad, hfin]
  have hrate : ∀ k < s.nb, ∀ c : Fin 13, c.val < 9 →
      s.I σ k c = s.O σ k c + (s.vals σ).getD (17 * k / 2 + c) 0 := by
    intro k hk c hc
    rw [rate_of_check h hat hk c hc, hpad, word_zero, add_zero, srcVal_getD]
    rfl
  have hcap : ∀ k < s.nb, ∀ c : Fin 13, 9 ≤ c.val → s.I σ k c = s.O σ k c :=
    fun k hk c hc => cap_of_check h hat hk c hc
  have hK : ∀ k < s.nb, KeccakCellsRelation (s.I σ k) (inLayout k) (s.O σ (k + 1)) (outLayout s.nb k)
      .all :=
    fun k hk => keccak_of_check h hat hk
  have hO0 : s.O σ 0 = cellsOfState (absorbChunks n zeroState pre) false := by
    funext c; simp only [O, ↓reduceIte]; exact h0 c
  have hB' : 16 * (s.vals σ).length = rate * s.nb := by rw [hvl]; exact hB
  obtain ⟨hw, hl⟩ := keccak_whole hpre hB' hO0 hrate hcap hK
  refine ⟨fun c => ?_, hl⟩
  have : s.O σ s.nb c = σ (s.outV (s.nb - 1) c) := by
    have := out_of_check h hat (k := s.nb - 1) (by omega) c
      (by rw [outs_whole h hfin (by omega)]; exact c.isLt)
    rw [Nat.sub_add_cancel (by omega)] at this
    exact this.symm
  rw [← this, hw]

end
end LeanVM.Guest.B1.Digest
