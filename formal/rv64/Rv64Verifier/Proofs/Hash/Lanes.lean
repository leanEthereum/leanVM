import Rv64Verifier.Model.Hash
import Rv64Verifier.Proofs.Hash.Run

/-!
# Keccak-f's round, lane by lane

`keccakRoundRust` (`Model/Hash.lean`) in the three stages the image computes it in: θ
(`thetaRust`, lane `i` is `theta`), ρ and π into `b` (`rhoPiRust`, the Rust's loop), χ and ι
(`chiRust`, lane `i` is `chi`). The `…E` functions build the same lanes as executor expressions
(`E`), so a block's lanes are compared with them modulo AC by the kernel; `thetaE_eval` and
`chiE_eval` read them back.
-/

namespace Rv64Verifier.Hash
open RiscvZkvm.Rv64 Rv64Verifier.Sym Rv64Verifier.Model

/-! ## The stages -/

/-- θ's column parity `C[x]`, as `keccak_f` computes it. -/
def col (a : Nat → Word) (x : Nat) : Word :=
  a x ^^^ a (x + 5) ^^^ a (x + 10) ^^^ a (x + 15) ^^^ a (x + 20)

/-- Lane `i` after θ. -/
def theta (a : Nat → Word) (i : Nat) : Word :=
  a i ^^^ (col a ((i % 5 + 4) % 5) ^^^ (col a ((i % 5 + 1) % 5)).rotateLeft 1)

/-- Lane `i` after χ, from `b`. -/
def chi (b : Nat → Word) (i : Nat) : Word :=
  b i ^^^ (~~~ b (5 * (i / 5) + (i % 5 + 1) % 5) &&& b (5 * (i / 5) + (i % 5 + 2) % 5))

/-- θ, the first loops of `keccak_f`'s body. -/
def thetaRust (a : List Word) : List Word :=
  let c := (List.range 5).map fun x ↦
    a.getD x 0 ^^^ a.getD (x + 5) 0 ^^^ a.getD (x + 10) 0 ^^^ a.getD (x + 15) 0 ^^^ a.getD (x + 20) 0
  let d := (List.range 5).map fun x ↦
    c.getD ((x + 4) % 5) 0 ^^^ (c.getD ((x + 1) % 5) 0).rotateLeft 1
  (List.range 5).foldl (fun a y ↦ (List.range 5).foldl
    (fun a x ↦ a.set (5 * y + x) (a.getD (5 * y + x) 0 ^^^ d.getD x 0)) a) a

/-- One step of the ρ and π loop. -/
def rhoPiStep (a b : List Word) (i : Nat) : List Word :=
  b.set (keccakPiRust.getD i 0) ((a.getD i 0).rotateLeft (keccakRhoRust.getD i 0))

/-- ρ and π into `b`. -/
def rhoPiRust (a : List Word) : List Word :=
  (List.range 25).foldl (rhoPiStep a) (List.replicate 25 0)

/-- χ from `b` into `a`, then ι. -/
def chiRust (a b : List Word) (rc : Word) : List Word :=
  let a := (List.range 5).foldl (fun a y ↦ (List.range 5).foldl
    (fun a x ↦ a.set (5 * y + x) (b.getD (5 * y + x) 0 ^^^
      (~~~ b.getD (5 * y + (x + 1) % 5) 0 &&& b.getD (5 * y + (x + 2) % 5) 0))) a) a
  a.set 0 (a.getD 0 0 ^^^ rc)

theorem keccakRoundRust_stages (a : List Word) (rc : Word) :
    keccakRoundRust a rc = chiRust (thetaRust a) (rhoPiRust (thetaRust a)) rc := rfl

theorem range25 : List.range 25 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18,
    19, 20, 21, 22, 23, 24] := rfl

theorem range5 : List.range 5 = [0, 1, 2, 3, 4] := rfl

theorem eq_of_length25 {a : List Word} (h : a.length = 25) : ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
    a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24, a = [a0, a1, a2, a3, a4, a5, a6, a7,
      a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24] := by
  match a, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
      a20, a21, a22, a23, a24], _ =>
    exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
      a19, a20, a21, a22, a23, a24, rfl⟩

theorem thetaRust_eq {a : List Word} (h : a.length = 25) :
    thetaRust a = (List.range 25).map (theta fun j ↦ a.getD j 0) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21, a22, a23, a24, rfl⟩ := eq_of_length25 h
  simp [thetaRust, theta, col, range5, range25]

theorem chiRust_eq {a b : List Word} (ha : a.length = 25) (hb : b.length = 25) (rc : Word) :
    chiRust a b rc = (List.range 25).map fun i ↦
      chi (fun j ↦ b.getD j 0) i ^^^ (if i = 0 then rc else 0) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21, a22, a23, a24, rfl⟩ := eq_of_length25 ha
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18,
    b19, b20, b21, b22, b23, b24, rfl⟩ := eq_of_length25 hb
  simp [chiRust, chi, range5, range25]

theorem length_thetaRust {a : List Word} (h : a.length = 25) : (thetaRust a).length = 25 := by
  rw [thetaRust_eq h]; simp

theorem length_rhoPiStep (a b : List Word) (i : Nat) : (rhoPiStep a b i).length = b.length :=
  List.length_set ..

theorem length_rhoPiRust (a : List Word) : (rhoPiRust a).length = 25 := by
  suffices ∀ (l : List Nat) (b : List Word), (l.foldl (rhoPiStep a) b).length = b.length by
    rw [rhoPiRust, this]; simp
  intro l
  induction l with
  | nil => intro b; rfl
  | cons i l ih => intro b; rw [List.foldl_cons, ih, length_rhoPiStep]

theorem length_chiRust {a b : List Word} (ha : a.length = 25) (hb : b.length = 25) (rc : Word) :
    (chiRust a b rc).length = 25 := by
  rw [chiRust_eq ha hb]; simp

theorem length_keccakRoundRust {a : List Word} (h : a.length = 25) (rc : Word) :
    (keccakRoundRust a rc).length = 25 := by
  rw [keccakRoundRust_stages]
  exact length_chiRust (length_thetaRust h) (length_rhoPiRust _) rc

/-- The lanes after `k` rounds. -/
def rounds (a : List Word) (k : Nat) : List Word := (keccakRCRust.take k).foldl keccakRoundRust a

theorem rounds_zero (a : List Word) : rounds a 0 = a := rfl

theorem foldl_take_succ {α β : Type} (f : α → β → α) (a : α) (d : β) (l : List β) {k : Nat}
    (hk : k < l.length) : (l.take (k + 1)).foldl f a = f ((l.take k).foldl f a) (l.getD k d) := by
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem hk, List.getD_eq_getElem _ _ hk]
  rfl

theorem length_keccakRCRust : keccakRCRust.length = 24 := rfl

theorem rounds_succ (a : List Word) {k : Nat} (hk : k < 24) :
    rounds a (k + 1) = keccakRoundRust (rounds a k) (keccakRCRust.getD k 0) :=
  foldl_take_succ _ _ _ _ (by rw [length_keccakRCRust]; exact hk)

theorem rounds_24 (a : List Word) : rounds a 24 = keccakFRust a := by
  rw [rounds, List.take_of_length_le (by rw [length_keccakRCRust])]
  rfl

theorem length_rounds {a : List Word} (h : a.length = 25) (k : Nat) : (rounds a k).length = 25 := by
  unfold rounds
  generalize keccakRCRust.take k = l
  induction l generalizing a with
  | nil => exact h
  | cons rc l ih => rw [List.foldl_cons]; exact ih (length_keccakRoundRust h rc)

/-! ## The same, as executor expressions -/

/-- `x` rotated left by `n`, as `slli`, `srli` and `or` compute it. -/
def rotE (e : E) (n : Nat) : E :=
  .bin .or (.bin .sll e (.c (BitVec.ofNat 64 n))) (.bin .srl e (.c (BitVec.ofNat 64 (64 - n))))

def colE (a : Nat → E) (x : Nat) : E :=
  .bin .xor (.bin .xor (.bin .xor (.bin .xor (a x) (a (x + 5))) (a (x + 10))) (a (x + 15)))
    (a (x + 20))

def thetaE (a : Nat → E) (i : Nat) : E :=
  .bin .xor (a i) (.bin .xor (colE a ((i % 5 + 4) % 5)) (rotE (colE a ((i % 5 + 1) % 5)) 1))

/-- `~~~x`, as `xori x, -1` computes it. -/
def notE (e : E) : E := .bin .xor e (.c (BitVec.allOnes 64))

def chiE (b : Nat → E) (i : Nat) : E :=
  .bin .xor (b i) (.bin .and (notE (b (5 * (i / 5) + (i % 5 + 1) % 5)))
    (b (5 * (i / 5) + (i % 5 + 2) % 5)))

theorem rotE_eval (s : MachineState) (e : E) {n : Nat} (h0 : 0 < n) (h : n < 64) :
    (rotE e n).eval s = (e.eval s).rotateLeft n := by
  simp only [rotE, E.eval, BinOp.eval, BitVec.toNat_ofNat, BitVec.rotateLeft_def]
  rw [Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 64 - n < 2 ^ 64),
    Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega : 64 - n < 64)]

theorem notE_eval (s : MachineState) (e : E) : (notE e).eval s = ~~~ e.eval s := by
  simp only [notE, E.eval, BinOp.eval, BitVec.xor_allOnes]

theorem colE_eval (s : MachineState) (a : Nat → E) (x : Nat) :
    (colE a x).eval s = col (fun j ↦ (a j).eval s) x := rfl

theorem thetaE_eval (s : MachineState) (a : Nat → E) (i : Nat) :
    (thetaE a i).eval s = theta (fun j ↦ (a j).eval s) i := by
  simp only [thetaE, theta, E.eval, BinOp.eval, rotE_eval s _ (by decide : 0 < 1) (by decide),
    colE_eval]

theorem chiE_eval (s : MachineState) (b : Nat → E) (i : Nat) :
    (chiE b i).eval s = chi (fun j ↦ (b j).eval s) i := by
  simp only [chiE, chi, E.eval, BinOp.eval, notE_eval]

end Rv64Verifier.Hash
