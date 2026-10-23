import LeanVM.Protocol.Flock

/-!
# Flock phase tests

The Flock argument is generic over its sizes; leanVM's (`2 ^ 14` positions a block, 64 skipped
coordinates) are too large for the interpreter, so the honest run is on a tiny argument over `E`
and the leanVM sizes are checked by theorems.

* **A tiny argument.** Two skipped values (`s = 1`), one within-block coordinate (`m = 1`), two
  blocks (`κ = 1`), one fixed coordinate of the point and one drawn; a four-wire circuit: the
  constant at position 0, inputs `x` and `y` at 1 and 2, `x ∧ y` at 3. The batch holds two
  satisfying blocks, `x = 1, y = 0` and `x = y = 1`.
* **The predicate.** The honest batch satisfies it; the zero batch satisfies every row (the rows
  are homogeneous) and fails only at the constant position; a wrong gate fails. Block 0 carries
  `x ≠ y`, so that its residual off the skip nodes is not zero.
* **An honest run, by hand.** Every statement the verifier hands on is in the relation the
  completeness proof threads, every check passes: the point, the skip message and the
  interpolated claim, the two normalized zerocheck rounds, `â, b̂`, `α`, the lincheck round, the
  slices against the native terminal, the ring-switching coefficient, and the weighted claim,
  which holds of the packed table.
* **What is rejected.** A wrong skip value gives a false claim, a wrong terminal value a false
  triple, wrong slices fail the native terminal and give a false weighted claim.
* **The round at `r_eq = 1`.** The point's drawn coordinate is `1`: the honest round message
  there, with a nonzero constant coefficient, passes the normalized check; the message with the
  constant coefficient the pinned Rust prover derives through `(1 + r)⁻¹` (zero at `r = 1`)
  evaluates to a false claim.
* **leanVM's sizes.** The schedule of the generic argument at `6, 8, k` is the spine's slot; the
  constants against the Python verifier; the zero region fails `FlockRegion.Holds` for every
  circuit, at the constant position.

A plain file, so `#guard` evaluates the compiled definitions. Values of `E` written with numerals
are named as definitions before a guard uses them.
-/

namespace LeanVMTests.Protocol.Flock

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Flock CompPoly CMlPolynomialEval
  SumcheckRound BlockR1CS

/-! ## A tiny argument -/

/-- No oracle. -/
def noO : ∀ i, NoOracle i := fun i ↦ i.elim0

def n0 : E := y
def n1 : E := y + 1
def n2 : E := y * y
def n3 : E := y * y + 1
def f0 : E := y * y + y

/-- Two skip nodes and their coset; the point's first coordinate fixed, the second drawn. -/
def toyP : Flock.Params E where
  s := 1
  m := 1
  κ := 1
  nodes := SkipDomain.ofPts #v[n0, n1, n2, n3]
  nFix := 1
  nRand := 1
  fixed := #v[f0]
  hpoint := rfl
  cpos := 0

/-- Row `k` of `A`: the constant, `x`, `y`, and `x` again for the gate. -/
def toyA (k j : Fin 4) : Bool := j.val == if k.val = 3 then 1 else k.val

/-- Row `k` of `B`: the constant, except `y` for the gate. -/
def toyB (k j : Fin 4) : Bool := j.val == if k.val = 3 then 2 else 0

/-- The four-wire circuit. -/
def toyC : BlockR1CS E (toyP.s + toyP.m) := BlockR1CS.ofMatrices toyA toyB

/-- The batch: block 0 is `(1, x = 1, y = 0, 0)`, block 1 is `(1, 1, 1, 1)`; table `i` holds
position `i + 2·jin` of block `t` at entry `jin + 2t`. -/
def toyZ (_ : ∀ i, NoOracle i) (_ : Fin (2 ^ toyP.s)) : CMlPolynomialEval E (toyP.m + toyP.κ) :=
  #v[1, 0, 1, 1]

/-- The zero batch. -/
def zeroZ (_ : ∀ i, NoOracle i) (_ : Fin (2 ^ toyP.s)) : CMlPolynomialEval E (toyP.m + toyP.κ) :=
  #v[0, 0, 0, 0]

/-- A batch whose gate in block 1 is wrong. -/
def badZ (_ : ∀ i, NoOracle i) (i : Fin (2 ^ toyP.s)) : CMlPolynomialEval E (toyP.m + toyP.κ) :=
  if i.val = 1 then #v[1, 0, 1, 0] else #v[1, 0, 1, 1]

#guard BatchHolds toyC toyP.cpos (toyZ noO)
#guard ¬ BatchHolds toyC toyP.cpos (zeroZ noO)
#guard ∀ i (u : Fin 4), (errTable toyC (zeroZ noO) i)[u] = 0
#guard ¬ BatchHolds toyC toyP.cpos (badZ noO)

/-- Nothing else is carried. -/
def side0 : Unit → (∀ i, NoOracle i) → Prop := fun _ _ ↦ True

instance (s : Unit) (o : ∀ i, NoOracle i) : Decidable (side0 s o) := inferInstanceAs (Decidable True)

/-! ## An honest run -/

/-- A challenge with three nonzero limbs. -/
def ch (a b c : ℕ) : E := E.ofLimbs (K.ofBits a) (K.ofBits b) (K.ofBits c)

/-- The drawn coordinate of the point: `1`, so that the second zerocheck round has `r = 1`. -/
def x1 : E := 1

def s1 : PointStmt Unit E 1 := ((), #v[x1])

#guard ((s1, noO), ()) ∈ pointRel toyP toyC toyZ side0 1

/-- The prover's skip message: `P` on the coset. -/
def msg : Vector E 2 := skipHonest toyP toyC toyZ ((s1, noO), ())

def zs : E := ch 0x1234 0x5678 0x9ABC

def st0 : Stmt (ZcX Unit E 2) E 0 := skipNext toyP (s1, msg) zs

#guard ((st0, noO), ()) ∈ rel (zcFamily toyP toyC toyZ side0) 0

/-- The zerocheck's first round. -/
def q0 : Message E 2 := (zcFamily toyP toyC toyZ side0).poly ((st0.1, noO), ()) 0 #v[]

#guard check 0 (zcFamily toyP toyC toyZ side0 (W := Unit)).weight st0 q0

def c0 : E := ch 0x2468 0x1357 0xBEEF

def st1 : Stmt (ZcX Unit E 2) E 1 := next 0 st0 (evaluate 2 q0 c0) c0

#guard ((st1, noO), ()) ∈ rel (zcFamily toyP toyC toyZ side0) 1

/-- The zerocheck's second round, at the point's coordinate `1`. -/
def q1 : Message E 2 := (zcFamily toyP toyC toyZ side0).poly ((st1.1, noO), ()) 1 st1.2.1

#guard check 1 (zcFamily toyP toyC toyZ side0 (W := Unit)).weight st1 q1

def c1 : E := ch 0xCAFE 0xF00D 0x4321

def st2 : Stmt (ZcX Unit E 2) E 2 := next 1 st1 (evaluate 2 q1 c1) c1

#guard ((st2, noO), ()) ∈ rel (zcFamily toyP toyC toyZ side0) 2

/-- The terminal values `â, b̂`; the verifier derives `ĉ`. -/
def tv : Vector E 2 := termHonest toyP toyC toyZ ((st2, noO), ())

def t2 : TermStmt Unit E 2 := termNext st2 tv

#guard ((t2, noO), ()) ∈ termRel toyP toyC toyZ side0

def α0 : E := ch 0x7777 0x3141 0x2718

def l0 : Stmt (LinX Unit E 2) E 0 := alphaNext t2 α0

#guard ((l0, noO), ()) ∈ rel (linFamily toyP toyC toyZ side0) 0

/-- The lincheck's round. -/
def lq0 : Message E 2 := (linFamily toyP toyC toyZ side0).poly ((l0.1, noO), ()) 0 #v[]

#guard check 0 (linFamily toyP toyC toyZ side0 (W := Unit)).weight l0 lq0

def d0 : E := ch 0x1618 0x0BAD 0xFACE

def l1 : Stmt (LinX Unit E 2) E 1 := next 0 l0 (evaluate 2 lq0 d0) d0

#guard ((l1, noO), ()) ∈ rel (linFamily toyP toyC toyZ side0) 1

/-- The slices, checked against the native terminal. -/
def sv : Vector E 2 := linHonest toyP toyZ ((l1, noO), ())

#guard linCheck toyP toyC l1 sv

def out : OutStmt Unit E 2 1 := linNext toyP l1 sv

#guard ((out, noO), ()) ∈ outRel toyP toyZ side0

/-- The packed table: two bits a cell, by the powers of `y`. -/
def colT (_ : ∀ i, NoOracle i) : CMlPolynomialEval E 2 :=
  Vector.ofFn fun u ↦ (toyZ noO 0)[u] + (toyZ noO 1)[u] * y

#guard (((out, #v[]), noO), ()) ∈ ringRel toyP toyZ side0 0 (RingHom.id E) y 0

def f1 : E := ch 0xABCD 0x9999 0x0F0F

/-- The weighted claim after the one ring-switching coefficient. -/
def wt : Weight E 2 := ringWeight toyP 0 id out.2.1 #v[f1]
def target : E := ringTarget toyP 0 (RingHom.id E) y out.2.2 #v[f1]

#guard wt.pair (RingHom.id E) (colT noO) = target

/-! ## What is rejected -/

/-- A wrong skip value interpolates to a false claim. -/
def msgBad : Vector E 2 := #v[msg[0] + 1, msg[1]]

def st0Bad : Stmt (ZcX Unit E (toyP.m + toyP.κ)) E 0 := skipNext toyP (s1, msgBad) zs

#guard ((st0Bad, noO), ()) ∉ rel (zcFamily toyP toyC toyZ side0) 0

/-- A wrong `â` makes the triple false. -/
def tvBad : Vector E 2 := #v[tv[0] + 1, tv[1]]

def t2Bad : TermStmt Unit E (toyP.m + toyP.κ) := termNext st2 tvBad

#guard ((t2Bad, noO), ()) ∉ termRel toyP toyC toyZ side0

/-- Wrong slices fail the native terminal, and their weighted claim is false. -/
def svBad : Vector E 2 := #v[sv[0] + 1, sv[1]]

#guard ¬ linCheck toyP toyC l1 svBad
#guard (ringWeight toyP 0 id out.2.1 #v[f1]).pair (RingHom.id E) (colT noO) ≠
  ringTarget toyP 0 (RingHom.id E) y svBad #v[f1]

/-! ## The round at `r_eq = 1` -/

-- The second zerocheck round binds the point's coordinate `x1 = 1`.
#guard st1.1.2.1[1] = 1
-- The honest message has a nonzero constant coefficient and passes the normalized check.
#guard q1[0] ≠ 0
-- The pinned Rust prover derives the constant coefficient as `(claim + r·G(1))·(1 + r)⁻¹`, zero at
-- `r = 1`; that message evaluates to a false claim at the challenge.
def q1Rust : Message E 2 :=
  #v[(st1.2.2 + 1 * evaluate 2 q1 1) * (1 + 1 : E)⁻¹, q1[1], q1[2]]

def st2Rust : Stmt (ZcX Unit E (toyP.m + toyP.κ)) E 2 := next 1 st1 (evaluate 2 q1Rust c1) c1

#guard q1Rust ≠ q1
#guard ((st2Rust, noO), ()) ∉ rel (zcFamily toyP toyC toyZ side0) 2

/-! ## leanVM's sizes -/

-- The generic argument at `6, 8, k` is the spine's slot.
example (k : ℕ) : flockSlot E Flock.kSkip Flock.kIn k (k + 1) 5 = flockSlotOf k := rfl

-- The ring-switching shifts are `2^(5 - p)`, those of `Parameters.Flock`.
#guard (List.ofFn fun p : Fin 6 ↦ 2 ^ (5 - p.val)) = Flock.ringShifts.toList

-- The fourth fixed coordinate and a skip node, against the Python verifier
-- (`verifier.py:1091-1099`).
#guard toString Flock.fixedPoint[3] = "E(0xb996e3c1cf34ac2412fa45aa9a1825d135cfd1ab784e4bf6)"
#guard toString (Flock.skipNode 5) = "E(0x00000000000000000000000000000000512620375ed2a109)"

/-- The zero region fails the Flock predicate, whatever the circuit: the constant position is
part of it. -/
theorem not_holds_zero {S : Shape} (r : FlockRegion S) :
    ¬ r.Holds ⟨Vector.replicate _ 0⟩ := by
  intro h
  have h512 := (h ⟨0, Nat.two_pow_pos _⟩).2
  have hz : ∀ (i : Fin (2 ^ Flock.kSkip)) (u : Fin (2 ^ (8 + r.kBatch))),
      (bitTable (⟨Vector.replicate _ 0⟩ : Column (8 + r.kBatch)) i)[u] = 0 := by
    intro i u
    rw [bitTable_getElem]
    simp [cellBit]
  have hb : ∀ t (j : Fin (2 ^ (Flock.kSkip + Flock.kIn))),
      (BlockR1CS.batchBlock (s := Flock.kSkip) (m := Flock.kIn)
        (bitTable (⟨Vector.replicate _ 0⟩ : Column (8 + r.kBatch))) t)[j] = 0 := by
    intro t j
    obtain ⟨⟨i, jin⟩, rfl⟩ := (cubeSplit Flock.kSkip Flock.kIn).surjective j
    rw [cubeSplit_apply, BlockR1CS.batchBlock_cubeIndex, hz]
  rw [hb] at h512
  exact zero_ne_one h512

end LeanVMTests.Protocol.Flock
