import Rv64Verifier.Sym.Expr

/-!
# Normalization modulo associativity and commutativity

Compiled code computes `x ^^^ y ^^^ z` in whatever order and association it likes, so a block's
result is compared with a specification up to the associativity and commutativity of `&&&`,
`|||`, `^^^` and `*`. `E.acNorm` flattens every chain of one of these operations, sorts its
operands by a structural order (`E.cmp`) and rebuilds it; `E.acNorm_eval` says it keeps the
meaning, so `E.acEq a b` (the normal forms are equal) implies `a.eval s = b.eval s`. Products
stay opaque terms: nothing is distributed.
-/

namespace Rv64Verifier.Sym
open RiscvZkvm.Rv64

def BinOp.isAC : BinOp → Bool
  | .and | .or | .xor | .mul => true
  | _ => false

theorem BinOp.ac_assoc {op : BinOp} (h : op.isAC = true) (x y z : Word) :
    op.eval (op.eval x y) z = op.eval x (op.eval y z) := by
  cases op <;> simp [BinOp.isAC] at h <;>
    simp [BinOp.eval, BitVec.and_assoc, BitVec.or_assoc, BitVec.xor_assoc, BitVec.mul_assoc]

theorem BinOp.ac_comm {op : BinOp} (h : op.isAC = true) (x y : Word) :
    op.eval x y = op.eval y x := by
  cases op <;> simp [BinOp.isAC] at h <;>
    simp [BinOp.eval, BitVec.and_comm, BitVec.or_comm, BitVec.xor_comm, BitVec.mul_comm]

theorem BinOp.ac_left_comm {op : BinOp} (h : op.isAC = true) (x y z : Word) :
    op.eval x (op.eval y z) = op.eval y (op.eval x z) := by
  rw [← BinOp.ac_assoc h, BinOp.ac_comm h x y, BinOp.ac_assoc h]

/-! ## A structural order -/

def wordOpCode : WordOp → Nat
  | .add => 0 | .sub => 1 | .sll => 2 | .srl => 3 | .sra => 4
  | .mul => 5 | .div => 6 | .divu => 7 | .rem => 8 | .remu => 9

def StoreKind.code : StoreKind → Nat
  | .d => 0 | .w => 1 | .h => 2 | .b => 3

def LoadKind.code : LoadKind → Nat
  | .d => 0 | .w => 1 | .wu => 2 | .h => 3 | .hu => 4 | .b => 5 | .bu => 6

def BinOp.code : BinOp → Nat
  | .add => 0 | .sub => 1 | .and => 2 | .or => 3 | .xor => 4 | .sll => 5 | .srl => 6
  | .sra => 7 | .slt => 8 | .sltu => 9 | .mul => 10 | .mulh => 11 | .mulhsu => 12
  | .mulhu => 13 | .div => 14 | .divu => 15 | .rem => 16 | .remu => 17
  | .w op => 18 + wordOpCode op
  | .st k bo => 28 + k.code + 4 * bo
  | .ldx k => 60 + k.code

def UnOp.code : UnOp → Nat
  | .ld k bo => k.code + 8 * bo

def CmpOp.code : CmpOp → Nat
  | .eq => 0 | .ne => 1 | .lt => 2 | .ge => 3 | .ltu => 4 | .geu => 5

def E.tag : E → Nat
  | .c _ => 0 | .reg _ => 1 | .ld _ => 2 | .un .. => 3 | .bin .. => 4 | .ite .. => 5 | .stx .. => 6

def natCmp (a b : Nat) : Ordering :=
  if a < b then .lt else if a = b then .eq else .gt

/-- A structural total order on expressions; only the canonicity of `E.acNorm` depends on it. -/
def E.cmp : E → E → Ordering
  | .c x, .c y => natCmp x.toNat y.toNat
  | .reg a, .reg b => natCmp a.toNat b.toNat
  | .ld a, .ld b => E.cmp a b
  | .un o a, .un o' b => (natCmp o.code o'.code).then (E.cmp a b)
  | .bin o a b, .bin o' a' b' => (natCmp o.code o'.code).then ((E.cmp a a').then (E.cmp b b'))
  | .ite o x y a b, .ite o' x' y' a' b' =>
    (natCmp o.code o'.code).then ((E.cmp x x').then ((E.cmp y y').then
      ((E.cmp a a').then (E.cmp b b'))))
  | .stx k o p v, .stx k' o' p' v' =>
    (natCmp k.code k'.code).then ((E.cmp o o').then ((E.cmp p p').then (E.cmp v v')))
  | a, b => natCmp a.tag b.tag

def E.lt (a b : E) : Bool :=
  match E.cmp a b with
  | .lt => true
  | _ => false

/-! ## Chains -/

/-- The operands of the maximal chain of `op` at the root of an expression. -/
def E.chain (op : BinOp) : E → List E
  | .bin op' a b => if op' = op then E.chain op a ++ E.chain op b else [.bin op' a b]
  | e => [e]

/-- A chain from its operands, associated to the right. -/
def E.rebuild (op : BinOp) : List E → E
  | [] => .c 0
  | [e] => e
  | e :: es => .bin op e (E.rebuild op es)

def E.insert (x : E) : List E → List E
  | [] => [x]
  | y :: ys => if E.lt y x then y :: E.insert x ys else x :: y :: ys

def E.sort : List E → List E
  | [] => []
  | x :: xs => E.insert x (E.sort xs)

/-- Normal form modulo associativity and commutativity of `&&&`, `|||`, `^^^` and `*`. -/
def E.acNorm : E → E
  | .c v => .c v
  | .reg r => .reg r
  | .ld a => .ld a.acNorm
  | .un op a => .un op a.acNorm
  | .bin op a b =>
    if op.isAC then E.rebuild op (E.sort (E.chain op a.acNorm ++ E.chain op b.acNorm))
    else .bin op a.acNorm b.acNorm
  | .ite op x y a b => .ite op x.acNorm y.acNorm a.acNorm b.acNorm
  | .stx k o p v => .stx k o.acNorm p.acNorm v.acNorm

/-- Equality modulo associativity and commutativity. -/
def E.acEq (a b : E) : Bool := E.beq a.acNorm b.acNorm

/-! ## Soundness -/

section
variable (s : MachineState) {op : BinOp}

theorem E.chain_ne_nil (e : E) : E.chain op e ≠ [] := by
  induction e with
  | bin op' a b iha _ =>
    simp only [E.chain]
    split
    · intro h; exact iha (List.append_eq_nil_iff.mp h).1
    · exact List.cons_ne_nil _ _
  | _ => exact List.cons_ne_nil _ _

theorem E.rebuild_cons (e : E) (es : List E) (h : es ≠ []) :
    (E.rebuild op (e :: es)).eval s = op.eval (e.eval s) ((E.rebuild op es).eval s) := by
  cases es with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

theorem E.rebuild_append (hop : op.isAC = true) :
    ∀ l₁ l₂ : List E, l₁ ≠ [] → l₂ ≠ [] →
      (E.rebuild op (l₁ ++ l₂)).eval s =
        op.eval ((E.rebuild op l₁).eval s) ((E.rebuild op l₂).eval s)
  | [], _, h, _ => absurd rfl h
  | [e], l₂, _, h₂ => E.rebuild_cons s e l₂ h₂
  | e :: e' :: rest, l₂, _, h₂ => by
    rw [List.cons_append, E.rebuild_cons s e (e' :: rest ++ l₂) (by simp),
      E.rebuild_append hop (e' :: rest) l₂ (List.cons_ne_nil _ _) h₂,
      E.rebuild_cons s e (e' :: rest) (List.cons_ne_nil _ _), BinOp.ac_assoc hop]

theorem E.rebuild_chain (hop : op.isAC = true) (e : E) :
    (E.rebuild op (E.chain op e)).eval s = e.eval s := by
  induction e with
  | bin op' a b iha ihb =>
    simp only [E.chain]
    split
    · rename_i h
      subst h
      rw [E.rebuild_append s hop _ _ (E.chain_ne_nil a) (E.chain_ne_nil b), iha, ihb]
      rfl
    · rfl
  | _ => rfl

theorem E.insert_ne_nil (x : E) : ∀ l : List E, E.insert x l ≠ []
  | [] => List.cons_ne_nil _ _
  | y :: ys => by
    show (if E.lt y x then y :: E.insert x ys else x :: y :: ys) ≠ []
    split <;> exact List.cons_ne_nil _ _

theorem E.rebuild_insert (hop : op.isAC = true) (x : E) :
    ∀ l : List E, (E.rebuild op (E.insert x l)).eval s = (E.rebuild op (x :: l)).eval s
  | [] => rfl
  | y :: ys => by
    have ih := E.rebuild_insert hop x ys
    show (E.rebuild op (if E.lt y x then y :: E.insert x ys else x :: y :: ys)).eval s = _
    split
    · rw [E.rebuild_cons s y _ (E.insert_ne_nil x ys), ih]
      cases ys with
      | nil => exact BinOp.ac_comm hop _ _
      | cons z zs =>
        rw [E.rebuild_cons s x (z :: zs) (List.cons_ne_nil _ _),
          E.rebuild_cons s x (y :: z :: zs) (List.cons_ne_nil _ _),
          E.rebuild_cons s y (z :: zs) (List.cons_ne_nil _ _), BinOp.ac_left_comm hop]
    · rfl

theorem E.sort_ne_nil : ∀ {l : List E}, l ≠ [] → E.sort l ≠ []
  | [], h => absurd rfl h
  | x :: _, _ => E.insert_ne_nil x _

theorem E.rebuild_sort (hop : op.isAC = true) :
    ∀ l : List E, (E.rebuild op (E.sort l)).eval s = (E.rebuild op l).eval s
  | [] => rfl
  | x :: xs => by
    have ih := E.rebuild_sort hop xs
    show (E.rebuild op (E.insert x (E.sort xs))).eval s = _
    rw [E.rebuild_insert s hop]
    cases xs with
    | nil => rfl
    | cons y ys =>
      rw [E.rebuild_cons s x _ (E.sort_ne_nil (List.cons_ne_nil y ys)), ih,
        E.rebuild_cons s x (y :: ys) (List.cons_ne_nil y ys)]

theorem E.acNorm_eval (e : E) : e.acNorm.eval s = e.eval s := by
  induction e with
  | c v => rfl
  | reg r => rfl
  | ld a ih => simp only [E.acNorm, E.eval, ih]
  | un o a ih => simp only [E.acNorm, E.eval, ih]
  | bin o a b iha ihb =>
    simp only [E.acNorm]
    split
    · rename_i hop
      rw [E.rebuild_sort s hop,
        E.rebuild_append s hop _ _ (E.chain_ne_nil _) (E.chain_ne_nil _),
        E.rebuild_chain s hop, E.rebuild_chain s hop, iha, ihb]
      rfl
    · simp only [E.eval, iha, ihb]
  | ite o x y a b ihx ihy iha ihb => simp only [E.acNorm, E.eval, ihx, ihy, iha, ihb]
  | stx k o p v iho ihp ihv => simp only [E.acNorm, E.eval, iho, ihp, ihv]

theorem E.acEq_eval {a b : E} (h : E.acEq a b = true) : a.eval s = b.eval s := by
  rw [← E.acNorm_eval s a, ← E.acNorm_eval s b, E.beq_eq h]

end

end Rv64Verifier.Sym
