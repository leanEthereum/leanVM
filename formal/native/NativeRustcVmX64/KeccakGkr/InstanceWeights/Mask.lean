module

public import NativeRustcX64.Sym
public import NativeVm.Equiv.KeccakRmfe
public import NativeRustcVm.MemLemmas

/-!
# `instance_weights`: the sums as masks (x86-64)

rustc unrolled `instance_weights`' sums: each word of each weight is an `xor` tree of the powers'
words, each selected by `cmovae` on the carry of a raw `bt` of a literal mask at the literal
loop counter. The symbolic executor leaves such a word as an `xor` tree of `ite`s, on closed
conditions (`cbool`, `cbool_eval`), between loads from the powers' buffer (`112` bytes into the
frame) and `0`. `symMask` reads such a tree as the set of powers it sums (a bit mask), `xorOf` sums
a mask's words (`symMask_eval`); the model's weight `e` is the sum over `rmfeEmbedW[e]`'s bits
(`iw_word`). `wordW` finds the word a list of writes left at an offset (`wordW_findWrite`).
-/

namespace NativeRustcVmX64.KeccakGkr.InstanceWeights

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model LeanVM.Parameters

@[expose] public section

/-- The words `f b` of the bits `b < n` of `M`, summed. -/
def xorN (f : Nat → BitVec 64) (M : Nat) : Nat → BitVec 64
  | 0 => 0
  | n + 1 => xorN f M n ^^^ (if M.testBit n then f n else 0)

/-- The words `f b` of `M`'s bits `b < 24`, summed. -/
abbrev xorOf (f : Nat → BitVec 64) (M : Nat) : BitVec 64 := xorN f M 24

/-- The powers' buffer's offset in the frame. -/
abbrev powOff : Nat := 112

/-- A closed symbolic value's value: literals and binary operations of them. -/
def csym : Sym → Option (BitVec 64)
  | .lit n => some (BitVec.ofNat 64 n)
  | .bin op w a b =>
    match csym a, csym b with
    | some x, some y => some (op.apply w x y)
    | _, _ => none
  | _ => none

/-- A closed symbolic boolean's value: literals, negations, the top bit of a closed value. -/
def cbool : SBool → Option Bool
  | .lit b => some b
  | .not c => (cbool c).map (!·)
  | .msb w a => (csym a).map fun x ↦ (low w x).msb
  | _ => none

/-- The set of powers a tree of word `d` of the powers sums. -/
def symMask (d : Nat) : Sym → Option Nat
  | .lit n => if n = 0 then some 0 else none
  | .load r o n =>
    if r = 0 ∧ n = 8 ∧ powOff + d ≤ o ∧ (o - powOff - d) % 16 = 0 ∧ (o - powOff - d) / 16 < 24 then
      some (2 ^ ((o - powOff - d) / 16))
    else none
  | .bin op w a b =>
    if op = .xor ∧ w = .W64 then
      match symMask d a, symMask d b with
      | some x, some y => some (x ^^^ y)
      | _, _ => none
    else none
  | .ite c a b =>
    match cbool c with
    | some true => symMask d a
    | some false => symMask d b
    | none => none
  | _ => none

/-- The word a list of writes leaves at offset `o` of region `r`: the newest write covering it, if
it is the 8 bytes at `o` and no newer write touches them. -/
def wordW (r o : Nat) : List Write → Option Sym
  | [] => none
  | w :: ws =>
    if w.r = r ∧ w.off = o ∧ w.n = 8 then some w.v
    else if w.r ≠ r ∨ w.off + w.n ≤ o ∨ o + 8 ≤ w.off then wordW r o ws
    else none

/-- The mask of weight `e`: `RMFE_EMBED`'s word. -/
def iwMask (e : Nat) : Nat := (rmfeEmbedW.getD e 0).toNat % 2 ^ 24

/-- The word is the literal `16`. -/
def lenOk : Option Sym → Bool
  | some (.lit n) => n == 16
  | _ => false

/-- The word is a tree of word `d` of the powers with mask `M`. -/
def wordOk (d M : Nat) : Option Sym → Bool
  | some v => symMask d v == some M
  | none => false

/-- The frame's `Buf<EW, 16>`'s offset. -/
abbrev bufOff : Nat := 736

/-- What `instance_weights` leaves in its `Buf<EW, 16>` at `736` in the frame: the length word,
then each weight's two words with the weight's mask. -/
def itemsOk (mem : List Write) : Bool :=
  lenOk (wordW 0 bufOff mem) && (List.range 16).all fun e ↦ (List.range 2).all fun d ↦
    wordOk (8 * d) (iwMask e) (wordW 0 (bufOff + 8 + 16 * e + 8 * d) mem)

end

public section

theorem lenOk_eq {o : Option Sym} (h : lenOk o = true) : o = some (.lit 16) := by
  cases o with
  | none => simp [lenOk] at h
  | some v => cases v <;> simp [lenOk] at h ⊢; exact h

theorem wordOk_eq {d M : Nat} {o : Option Sym} (h : wordOk d M o = true) :
    ∃ v, o = some v ∧ symMask d v = some M := by
  cases o with
  | none => simp [wordOk] at h
  | some v => exact ⟨v, rfl, by simpa [wordOk] using h⟩

theorem xorN_zero (f : Nat → BitVec 64) (n : Nat) : xorN f 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [xorN, ih]

theorem ite_bne (p q : Bool) (x : BitVec 64) :
    (if (p != q) = true then x else 0) = (if p = true then x else 0) ^^^ (if q = true then x else 0) := by
  cases p <;> cases q <;> simp

theorem xorN_xor (f : Nat → BitVec 64) (M N n : Nat) :
    xorN f (M ^^^ N) n = xorN f M n ^^^ xorN f N n := by
  induction n with
  | zero => simp [xorN]
  | succ n ih =>
    simp only [xorN, ih, Nat.testBit_xor, ite_bne]
    ac_rfl

theorem xorN_pow (f : Nat → BitVec 64) {b n : Nat} (hb : b < n) : xorN f (2 ^ b) n = f b := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [xorN, Nat.testBit_two_pow]
    by_cases h : b = n
    · subst h
      simp [xorN_zero_of_lt]
    · rw [ih (by omega)]
      simp [h]
where
  xorN_zero_of_lt {b : Nat} : xorN f (2 ^ b) b = 0 := by
    suffices ∀ k ≤ b, xorN f (2 ^ b) k = 0 from this b (Nat.le_refl _)
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [xorN, ih (by omega), Nat.testBit_two_pow]
      simp [show b ≠ k by omega]

variable [Labels] (env : Env)

/-- A closed value's value. -/
theorem csym_eval : ∀ (t : Sym) (x : BitVec 64), csym t = some x → t.eval env = x
  | .lit n, x, h => by simp only [csym, Option.some.injEq] at h; subst h; rfl
  | .bin op w a b, x, h => by
    simp only [csym] at h
    split at h
    · rename_i x' y' ha hb
      cases h
      rw [Sym.eval, csym_eval a x' ha, csym_eval b y' hb]
    · cases h
  | .reg _, _, h => by simp [csym] at h
  | .var _, _, h => by simp [csym] at h
  | .ptr _ _, _, h => by simp [csym] at h
  | .label _, _, h => by simp [csym] at h
  | .gotSlot _, _, h => by simp [csym] at h
  | .load _ _ _, _, h => by simp [csym] at h
  | .loadx _ _ _ _, _, h => by simp [csym] at h
  | .retAddr, _, h => by simp [csym] at h
  | .un _ _ _, _, h => by simp [csym] at h
  | .tern _ _ _ _ _, _, h => by simp [csym] at h
  | .ite _ _ _, _, h => by simp [csym] at h

/-- A closed boolean's value. -/
theorem cbool_eval : ∀ (c : SBool) (x : Bool), cbool c = some x → c.eval env = x
  | .lit b, x, h => by simp only [cbool, Option.some.injEq] at h; subst h; rfl
  | .not c, x, h => by
    simp only [cbool, Option.map_eq_some_iff] at h
    obtain ⟨y, hy, rfl⟩ := h
    rw [SBool.eval, cbool_eval c y hy]
  | .msb w a, x, h => by
    simp only [cbool, Option.map_eq_some_iff] at h
    obtain ⟨y, hy, rfl⟩ := h
    rw [SBool.eval, csym_eval env a y hy]
  | .and _ _, _, h => by simp [cbool] at h
  | .or _ _, _, h => by simp [cbool] at h
  | .beq _ _, _, h => by simp [cbool] at h
  | .ite _ _ _, _, h => by simp [cbool] at h
  | .cmp _ _ _ _, _, h => by simp [cbool] at h
  | .flagCF, _, h => by simp [cbool] at h
  | .flagZF, _, h => by simp [cbool] at h
  | .flagSF, _, h => by simp [cbool] at h
  | .flagOF, _, h => by simp [cbool] at h

/-- **A tree's value** is its mask's sum of the powers' words. -/
theorem symMask_eval (d : Nat) :
    ∀ (t : Sym) (M : Nat), symMask d t = some M →
      t.eval env = xorOf (fun b ↦ env.load 0 (powOff + 16 * b + d) 8) M
  | .lit n, M, h => by
    simp only [symMask] at h
    split at h
    · cases h; subst n; simp [Sym.eval, xorOf, xorN_zero]
    · cases h
  | .load r o n, M, h => by
    simp only [symMask] at h
    split at h
    · rename_i hc
      obtain ⟨rfl, rfl, h1, h2, h3⟩ := hc
      cases h
      rw [xorOf, xorN_pow _ h3]
      show env.load 0 o 8 = _
      congr 1
      omega
    · cases h
  | .bin op w a b, M, h => by
    simp only [symMask] at h
    split at h
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      split at h
      · rename_i x y hx hy
        cases h
        rw [xorOf, xorN_xor, ← xorOf, ← xorOf, ← symMask_eval d a x hx,
          ← symMask_eval d b y hy]
        simp [Sym.eval, BinOp.apply]
      · cases h
    · cases h
  | .ite c a b, M, h => by
    simp only [symMask] at h
    split at h
    · rename_i hc
      rw [Sym.eval, cbool_eval env c true hc]
      exact symMask_eval d a M h
    · rename_i hc
      rw [Sym.eval, cbool_eval env c false hc]
      exact symMask_eval d b M h
    · cases h
  | .reg _, _, h => by simp [symMask] at h
  | .var _, _, h => by simp [symMask] at h
  | .ptr _ _, _, h => by simp [symMask] at h
  | .label _, _, h => by simp [symMask] at h
  | .gotSlot _, _, h => by simp [symMask] at h
  | .loadx _ _ _ _, _, h => by simp [symMask] at h
  | .retAddr, _, h => by simp [symMask] at h
  | .un _ _ _, _, h => by simp [symMask] at h
  | .tern _ _ _ _ _, _, h => by simp [symMask] at h

omit [Labels] in
/-- **The word a list of writes leaves**, byte by byte. -/
theorem wordW_findWrite {r o : Nat} :
    ∀ {mem : List Write} {v : Sym}, wordW r o mem = some v →
      ∀ i < 8, findWrite r (o + i) mem = some (v, i)
  | [], _, h => by simp [wordW] at h
  | w :: ws, v, h => by
    intro i hi
    simp only [wordW] at h
    rw [findWrite_cons]
    split at h
    · rename_i hc
      obtain ⟨h1, h2, h3⟩ := hc
      cases h
      split
      · congr; omega
      · rename_i hn; exact absurd ⟨h1, by omega, by omega⟩ hn
    · split at h
      · rename_i hc0 hc
        split
        · rename_i hn; omega
        · exact wordW_findWrite h i hi
      · cases h

omit [Labels] in
/-- A sum over a word's bits, word by word. -/
theorem sumE_bits (P : Nat → EW) (w : UInt64) (f : EW → UInt64)
    (hf : ∀ x y, f (x + y) = f x ^^^ f y) (h0 : f 0 = 0) {n : Nat} (hn : n ≤ 24) :
    (f (sumE ((Array.range n).filterMap fun b ↦ if testBitW w b then some (P b) else none))).toBitVec =
      xorN (fun b ↦ (f (P b)).toBitVec) (w.toNat % 2 ^ 24) n := by
  induction n with
  | zero =>
    have e0 : (Array.range 0).filterMap (fun b ↦ if testBitW w b then some (P b) else none) = #[] :=
      Array.toList_inj.mp (by rw [Array.toList_filterMap, Array.toList_range]; rfl)
    rw [e0]
    simp [sumE, xorN, h0]
  | succ n ih =>
    have e : (Array.range (n + 1)).filterMap (fun b ↦ if testBitW w b then some (P b) else none) =
        ((Array.range n).filterMap fun b ↦ if testBitW w b then some (P b) else none) ++
          (if testBitW w n then #[P n] else #[]) := by
      apply Array.toList_inj.mp
      rw [Array.toList_filterMap, Array.toList_range, List.range_succ, List.filterMap_append,
        Array.toList_append, Array.toList_filterMap, Array.toList_range]
      split <;> simp_all
    rw [e, xorN, ← ih (by omega), NativeVm.Equiv.testBitW_eq w (by omega), Nat.testBit_mod_two_pow,
      decide_eq_true (show n < 24 by omega), Bool.true_and]
    cases w.toNat.testBit n <;> simp [sumE, hf]

omit [Labels] in
/-- **The model's weight `e`**, word by word: the sum of the powers' words over its mask. -/
theorem iw_word (s : EW) {e : Nat} (he : e < 16) (f : EW → UInt64)
    (hf : ∀ x y, f (x + y) = f x ^^^ f y) (h0 : f 0 = 0) :
    (f ((keccakInstanceWeights s).getD e 0)).toBitVec =
      xorOf (fun b ↦ (f ((powers s 24).getD b 0)).toBitVec) (iwMask e) := by
  have hsz : e < rmfeEmbedW.size := by
    simp only [rmfeEmbedW, Array.size_map, List.size_toArray, NativeVm.Equiv.rmfeEmbed_length]
    exact he
  rw [keccakInstanceWeights, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_eq_getElem hsz, Option.map_some, Option.getD_some, iwMask,
    Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hsz, Option.getD_some]
  exact sumE_bits _ _ f hf h0 (Nat.le_refl _)

end

end NativeRustcVmX64.KeccakGkr.InstanceWeights
