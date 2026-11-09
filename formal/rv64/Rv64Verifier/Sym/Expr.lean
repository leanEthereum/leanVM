import Rv64Verifier.Machine

/-!
# Symbolic 64-bit word expressions

Ported from sig.golf's `SigGolfCandidate.Rv`.

`E` is a small expression language over atoms taken from a fixed initial machine state `s`:
`E.reg r` is the initial register value `s.getReg r`, and `E.ld a` the initial memory doubleword
`s.getMem (a.eval s)`. `E.eval s e : Word` is the meaning of `e` relative to `s`. The smart
constructors (`mkAdd`, `mkBin`, `mkUn`, `mkIte`) fold constants and normalize additive constants,
so that addresses have the shape `base + const`.

Memory accesses are checked as riscv-zkvm's `step` checks them (`validAccess`): a valid memory
window and natural alignment.
-/

namespace Rv64Verifier.Sym
open RiscvZkvm.Rv64

inductive LoadKind where
  | d | w | wu | h | hu | b | bu
  deriving DecidableEq, Repr

inductive StoreKind where
  | d | w | h | b
  deriving DecidableEq, Repr

def LoadKind.width : LoadKind → Nat
  | .d => 8 | .w => 4 | .wu => 4 | .h => 2 | .hu => 2 | .b => 1 | .bu => 1

def StoreKind.width : StoreKind → Nat
  | .d => 8 | .w => 4 | .h => 2 | .b => 1

/-- riscv-zkvm's check of a data access of `width` bytes at `a`, as `RiscvZkvm.Rv64.step` makes
it for each width. -/
def validAccess (width : Nat) (a : Word) : Bool :=
  match width with
  | 8 => isValidDwordAccess a
  | 4 => isValidMemAccess a
  | 2 => isValidHalfwordAccess a
  | _ => isValidByteAccess a

/-- The value a sub-doubleword load extracts from the containing doubleword `x`, at byte offset
`bo` (`0 ≤ bo < 8`). For `.d` it is the doubleword itself. -/
def LoadKind.fromWord : LoadKind → Word → Nat → Word
  | .d, x, _ => x
  | .w, x, bo => (extractWord32 x (bo / 4)).signExtend 64
  | .wu, x, bo => (extractWord32 x (bo / 4)).zeroExtend 64
  | .h, x, bo => (extractHalfword x (bo / 2)).signExtend 64
  | .hu, x, bo => (extractHalfword x (bo / 2)).zeroExtend 64
  | .b, x, bo => (extractByte x bo).signExtend 64
  | .bu, x, bo => (extractByte x bo).zeroExtend 64

/-- The doubleword after a sub-doubleword store of `v` at byte offset `bo` into `old`. -/
def StoreKind.merge : StoreKind → Word → Nat → Word → Word
  | .d, _, _, v => v
  | .w, old, bo, v => replaceWord32 old (bo / 4) (v.truncate 32)
  | .h, old, bo, v => replaceHalfword old (bo / 2) (v.truncate 16)
  | .b, old, bo, v => replaceByte old bo (v.truncate 8)

/-- Binary operations: the RV64IM ALU operations, the 32-bit word operations, and sub-doubleword
store merges. -/
inductive BinOp where
  | add | sub | and | or | xor | sll | srl | sra | slt | sltu
  | mul | mulh | mulhsu | mulhu | div | divu | rem | remu
  /-- a 32-bit word operation, sign-extended to 64 bits -/
  | w (op : WordOp)
  /-- sub-doubleword store merge: `eval old v = k.merge old bo v` -/
  | st (k : StoreKind) (bo : Nat)
  deriving DecidableEq, Repr

inductive UnOp where
  /-- sub-doubleword load extraction: `eval x = k.fromWord x bo` -/
  | ld (k : LoadKind) (bo : Nat)
  deriving DecidableEq, Repr

/-- Branch conditions. -/
inductive CmpOp where
  | eq | ne | lt | ge | ltu | geu
  deriving DecidableEq, Repr

def BinOp.eval : BinOp → Word → Word → Word
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .and, x, y => x &&& y
  | .or, x, y => x ||| y
  | .xor, x, y => x ^^^ y
  | .sll, x, y => x <<< (y.toNat % 64)
  | .srl, x, y => x >>> (y.toNat % 64)
  | .sra, x, y => BitVec.sshiftRight x (y.toNat % 64)
  | .slt, x, y => if BitVec.slt x y then 1 else 0
  | .sltu, x, y => if BitVec.ult x y then 1 else 0
  | .mul, x, y => x * y
  | .mulh, x, y => rv64_mulh x y
  | .mulhsu, x, y => rv64_mulhsu x y
  | .mulhu, x, y => rv64_mulhu x y
  | .div, x, y => rv64_div x y
  | .divu, x, y => rv64_divu x y
  | .rem, x, y => rv64_rem x y
  | .remu, x, y => rv64_remu x y
  | .w op, x, y => (wordResult op (x.truncate 32) (y.truncate 32)).signExtend 64
  | .st k bo, x, y => k.merge x bo y

def UnOp.eval : UnOp → Word → Word
  | .ld k bo, x => k.fromWord x bo

def CmpOp.eval : CmpOp → Word → Word → Bool
  | .eq, x, y => x == y
  | .ne, x, y => x != y
  | .lt, x, y => BitVec.slt x y
  | .ge, x, y => !BitVec.slt x y
  | .ltu, x, y => BitVec.ult x y
  | .geu, x, y => !BitVec.ult x y

/-- Symbolic 64-bit words. -/
inductive E where
  | c (v : Word)
  /-- initial register value (atom) -/
  | reg (r : Reg)
  /-- initial memory doubleword at the given address (atom) -/
  | ld (a : E)
  | un (op : UnOp) (a : E)
  | bin (op : BinOp) (a b : E)
  /-- `if op x y then a else b` -/
  | ite (op : CmpOp) (x y a b : E)
  deriving Repr

/-- Meaning of a symbolic word relative to the initial state `s`. -/
def E.eval (s : MachineState) : E → Word
  | .c v => v
  | .reg r => s.getReg r
  | .ld a => s.getMem (a.eval s)
  | .un op a => op.eval (a.eval s)
  | .bin op a b => op.eval (a.eval s) (b.eval s)
  | .ite op x y a b => if op.eval (x.eval s) (y.eval s) then a.eval s else b.eval s

/-! ## Boolean equality -/

def Reg.beqN (a b : Reg) : Bool := a.toNat == b.toNat

theorem Reg.toNat_inj {a b : Reg} (h : a.toNat = b.toNat) : a = b := by
  have key : ∀ r : Reg, RiscvZkvm.Interpreter.regOfBits (BitVec.ofNat 5 r.toNat) = r := by
    intro r; cases r <;> rfl
  rw [← key a, ← key b, h]

theorem Reg.beqN_eq {a b : Reg} (h : Reg.beqN a b = true) : a = b :=
  Reg.toNat_inj (by simpa [Reg.beqN] using h)

def E.beq : E → E → Bool
  | .c x, .c y => x.toNat == y.toNat
  | .reg a, .reg b => Reg.beqN a b
  | .ld a, .ld b => E.beq a b
  | .un o a, .un o' b => decide (o = o') && E.beq a b
  | .bin o a b, .bin o' a' b' => decide (o = o') && E.beq a a' && E.beq b b'
  | .ite o x y a b, .ite o' x' y' a' b' =>
      decide (o = o') && E.beq x x' && E.beq y y' && E.beq a a' && E.beq b b'
  | _, _ => false

theorem E.beq_eq : ∀ {a b : E}, E.beq a b = true → a = b := by
  intro a
  induction a with
  | c x => intro b h; cases b <;> simp [E.beq] at h; exact congrArg _ (BitVec.eq_of_toNat_eq h)
  | reg r => intro b h; cases b <;> simp [E.beq] at h; exact congrArg _ (Reg.beqN_eq h)
  | ld a ih => intro b h; cases b <;> simp [E.beq] at h; exact congrArg _ (ih h)
  | un o a ih =>
    intro b h; cases b <;> simp [E.beq] at h
    obtain ⟨h1, h2⟩ := h; subst h1; rw [ih h2]
  | bin o a b iha ihb =>
    intro b' h; cases b' <;> simp [E.beq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h; subst h1; rw [iha h2, ihb h3]
  | ite o x y a b ihx ihy iha ihb =>
    intro b' h; cases b' <;> simp [E.beq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h; subst h1; rw [ihx h2, ihy h3, iha h4, ihb h5]

/-! ## Smart constructors -/

/-- `a + k` with constant folding and offset merging. -/
def addC (a : E) (k : Word) : E :=
  match a with
  | .c x => .c (x + k)
  | .bin .add a' (.c x) => if (x + k).toNat == 0 then a' else .bin .add a' (.c (x + k))
  | a => if k.toNat == 0 then a else .bin .add a (.c k)

def mkAdd (a b : E) : E :=
  match b with
  | .c k => addC a k
  | b =>
    match a with
    | .c k => addC b k
    | a =>
      match b with
      | .bin .add b' (.c k) => addC (.bin .add a b') k
      | b => .bin .add a b

def mkBin (op : BinOp) (a b : E) : E :=
  match op with
  | .add => mkAdd a b
  | .sub =>
    match a, b with
    | .c x, .c y => .c (x - y)
    | a, .c y => addC a (-y)
    | a, b => .bin .sub a b
  | op =>
    match a, b with
    | .c x, .c y => .c (op.eval x y)
    | a, b => .bin op a b

def mkUn (op : UnOp) (a : E) : E :=
  match a with
  | .c x => .c (op.eval x)
  | a => .un op a

def mkIte (op : CmpOp) (x y a b : E) : E :=
  match x, y with
  | .c u, .c v => if op.eval u v then a else b
  | x, y => .ite op x y a b

theorem addC_eval (s : MachineState) (a : E) (k : Word) :
    (addC a k).eval s = a.eval s + k := by
  unfold addC
  split
  · rfl
  · rename_i a' x
    split
    · rename_i h
      have h0 : x + k = 0 := BitVec.eq_of_toNat_eq (by simpa using h)
      simp [E.eval, BinOp.eval, BitVec.add_assoc, h0]
    · simp [E.eval, BinOp.eval, BitVec.add_assoc]
  · split
    · rename_i h
      have h0 : k = 0 := BitVec.eq_of_toNat_eq (by simpa using h)
      simp [h0]
    · rfl

theorem mkAdd_eval (s : MachineState) (a b : E) :
    (mkAdd a b).eval s = a.eval s + b.eval s := by
  unfold mkAdd
  split
  · rw [addC_eval]; rfl
  · split
    · rw [addC_eval, BitVec.add_comm]; rfl
    · split
      · rw [addC_eval]; simp [E.eval, BinOp.eval, BitVec.add_assoc]
      · rfl

theorem mkBin_eval (s : MachineState) (op : BinOp) (a b : E) :
    (mkBin op a b).eval s = op.eval (a.eval s) (b.eval s) := by
  unfold mkBin
  split
  · exact mkAdd_eval s a b
  · split
    · rfl
    · rw [addC_eval]; simp [E.eval, BinOp.eval, BitVec.sub_eq_add_neg]
    · rfl
  · split
    · rfl
    · rfl

theorem mkUn_eval (s : MachineState) (op : UnOp) (a : E) :
    (mkUn op a).eval s = op.eval (a.eval s) := by
  unfold mkUn; split <;> rfl

theorem mkIte_eval (s : MachineState) (op : CmpOp) (x y a b : E) :
    (mkIte op x y a b).eval s =
      if op.eval (x.eval s) (y.eval s) then a.eval s else b.eval s := by
  unfold mkIte
  split
  · split <;> simp_all [E.eval]
  · rfl

/-! ## Addresses -/

/-- A normalized address: `base + off` (`base = none` means the constant `off`). -/
structure Addr where
  base : Option E
  off : Word
  deriving Repr

def Addr.eval (s : MachineState) (a : Addr) : Word :=
  match a.base with
  | none => a.off
  | some b => b.eval s + a.off

def Addr.toE (a : Addr) : E :=
  match a.base with
  | none => .c a.off
  | some b => addC b a.off

theorem Addr.toE_eval (s : MachineState) (a : Addr) : a.toE.eval s = a.eval s := by
  rcases a with ⟨_ | b, off⟩
  · rfl
  · simp [Addr.toE, Addr.eval, addC_eval]

/-- Split an expression into `(base, constant offset)`. -/
def norm : E → Addr
  | .c k => ⟨none, k⟩
  | .bin .add a (.c k) => ⟨some a, k⟩
  | e => ⟨some e, 0⟩

theorem norm_eval (s : MachineState) (e : E) : (norm e).eval s = e.eval s := by
  unfold norm
  split
  · rfl
  · rfl
  · simp [Addr.eval]

def Addr.beq (a b : Addr) : Bool :=
  (match a.base, b.base with
   | none, none => true
   | some x, some y => E.beq x y
   | _, _ => false) && a.off.toNat == b.off.toNat

theorem Addr.beq_eq {a b : Addr} (h : Addr.beq a b = true) : a = b := by
  rcases a with ⟨_ | x, o⟩ <;> rcases b with ⟨_ | y, o'⟩ <;> simp [Addr.beq] at h
  · rw [BitVec.eq_of_toNat_eq h]
  · rw [E.beq_eq h.1, BitVec.eq_of_toNat_eq h.2]

/-- Result of an aliasing query. -/
inductive Alias where
  | same | diff | unknown
  deriving DecidableEq, Repr

/-- Decide whether two addresses are equal, different, or undecidable (sound, syntactic). -/
def Addr.alias (a b : Addr) : Alias :=
  match a.base, b.base with
  | none, none => if a.off.toNat == b.off.toNat then .same else .diff
  | some x, some y =>
    if E.beq x y then (if a.off.toNat == b.off.toNat then .same else .diff) else .unknown
  | _, _ => .unknown

theorem Addr.alias_same {a b : Addr} (h : a.alias b = .same) (s : MachineState) :
    a.eval s = b.eval s := by
  rcases a with ⟨_ | x, o⟩ <;> rcases b with ⟨_ | y, o'⟩ <;>
    simp only [Addr.alias, Addr.eval] at h ⊢
  · split at h
    · rename_i h'; exact BitVec.eq_of_toNat_eq (by simpa using h')
    · cases h
  · cases h
  · cases h
  · split at h
    · rename_i hb; split at h
      · rename_i h'
        have h1 := E.beq_eq hb
        have h2 : o = o' := BitVec.eq_of_toNat_eq (by simpa using h')
        rw [h1, h2]
      · cases h
    · cases h

theorem Addr.alias_diff {a b : Addr} (h : a.alias b = .diff) (s : MachineState) :
    a.eval s ≠ b.eval s := by
  rcases a with ⟨_ | x, o⟩ <;> rcases b with ⟨_ | y, o'⟩ <;>
    simp only [Addr.alias, Addr.eval] at h ⊢
  · split at h
    · cases h
    · rename_i h'; intro heq; apply h'; simp [heq]
  · cases h
  · cases h
  · split at h
    · rename_i hb; split at h
      · cases h
      · rename_i h'; rw [E.beq_eq hb]; intro heq; apply h'
        have := (BitVec.add_right_inj _).mp heq
        simp [this]
    · cases h

/-! ## Side conditions -/

/-- Side conditions emitted by the symbolic executor. -/
inductive Oblig where
  /-- `validAccess w (a.eval s) = true` -/
  | valid (a : Addr) (w : Nat)
  /-- `(b.eval s).toNat % 8 = 0` (base of a sub-doubleword access) -/
  | align8 (b : E)
  /-- `a.eval s ≠ b.eval s` (only emitted in `noAlias` mode) -/
  | ne (a b : Addr)
  deriving Repr

def Oblig.holds (s : MachineState) : Oblig → Prop
  | .valid a w => validAccess w (a.eval s) = true
  | .align8 b => (b.eval s).toNat % 8 = 0
  | .ne a b => a.eval s ≠ b.eval s

def Oblig.beq : Oblig → Oblig → Bool
  | .valid a w, .valid b w' => Addr.beq a b && w == w'
  | .align8 a, .align8 b => E.beq a b
  | .ne a b, .ne a' b' => Addr.beq a a' && Addr.beq b b'
  | _, _ => false

theorem Oblig.beq_eq {a b : Oblig} (h : Oblig.beq a b = true) : a = b := by
  cases a <;> cases b <;> simp [Oblig.beq] at h
  · rw [Addr.beq_eq h.1, h.2]
  · rw [E.beq_eq h]
  · rw [Addr.beq_eq h.1, Addr.beq_eq h.2]

/-- All side conditions hold (a right-nested conjunction, simp-friendly). -/
def Oblig.all (s : MachineState) : List Oblig → Prop
  | [] => True
  | [o] => o.holds s
  | o :: os => o.holds s ∧ Oblig.all s os

theorem Oblig.all_iff (s : MachineState) (os : List Oblig) :
    Oblig.all s os ↔ ∀ o ∈ os, o.holds s := by
  induction os with
  | nil => simp [Oblig.all]
  | cons o os ih =>
    cases os with
    | nil => simp [Oblig.all]
    | cons o' os' => simp only [Oblig.all] at ih ⊢; simp [ih]

end Rv64Verifier.Sym
