module

public import Qrom.Bridge
public import VCVio.Quantum.Comp.Combinators

@[expose] public section

/-!
# Random oracles with overrides and classical side ports

A security game often answers some hash inputs from fixed data and the rest from the random
function `G`, and offers classical ports beside the hash, such as a signing oracle. Both may
depend on a classical side state `s : S`. `Qrom.OvGame` records the initial side state, the
overrides `ov s x` (`some d` answers `x` with `d`, `none` with `G x`) and the transition of each
side port. A side port reports its result together with the side state it read.

Three runtimes answer the signature `Qrom.ovSpec` (the hash port, then the side ports), each on a
private register `S × T`:

* `Qrom.OvGame.sampled g G`: `T = Unit`, the hash answered by the overridden function;
* `Qrom.OvGame.purified g`: `T = X → Y`, the function held in uniform superposition;
* `Qrom.OvGame.compressed g`: `T = Database X Y`, the compressed oracle with the overrides.

The hash ports are table oracles (`Quantum.tableOracle`) reading `S × T`; the compressed one is
conjugated by the compression of every cell, as Zhandry's compressed oracle is.
-/

open Matrix OracleSpec
open scoped Kronecker ENNReal

universe u v w

set_option linter.unusedSectionVars false

namespace Qrom

open Quantum

/-- Classical side ports: no quantum input, a classical result and the side state read. -/
@[reducible]
def sideSpec (S P : Type) (Res : P → Type) : QuantumOracleSpec.{0, 0} where
  Port := P
  In _ := QReg.of Unit
  Out _ := QReg.of Unit
  Result j := Res j × S

/-- The hash port, then the side ports. -/
@[reducible]
def ovSpec (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] (S P : Type)
    (Res : P → Type) : QuantumOracleSpec.{0, 0} :=
  (qromSpec X Y).sum (sideSpec S P Res)

/-- A game around a random function: the initial side state, the overrides of the hash, and the
transitions of the side ports. -/
structure OvGame (X Y S P : Type) (Res : P → Type) where
  /-- The initial side state. -/
  init : S
  /-- `ov s x = some d` answers the hash at `x` with `d` in side state `s`. -/
  ov : S → X → Option Y
  /-- The result and the next side state of each side port. -/
  trans : (j : P) → S → Res j × S

namespace OvGame

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {S P : Type} [Fintype S] [DecidableEq S] {Res : P → Type} [∀ j, Fintype (Res j)]
  [∀ j, DecidableEq (Res j)]
variable (g : OvGame X Y S P Res)

/-! ## Side ports -/

section side

variable (T : Type) [Fintype T] [DecidableEq T]

/-- The Kraus operator of the side port `j` with result `r` read in side state `s₀`: it keeps the
table and moves `s₀` to its successor, `|s'⟩⟨s₀| ⊗ 1`, when `r` is the result at `s₀`. -/
noncomputable def sideKraus (j : P) (rs : Res j × S) :
    Matrix (Unit × (S × T)) (Unit × (S × T)) ℂ :=
  (if (g.trans j rs.2).1 = rs.1 then (1 : ℂ) else 0) •
    ((1 : Matrix Unit Unit ℂ) ⊗ₖ (Matrix.single (g.trans j rs.2).2 rs.2 (1 : ℂ) ⊗ₖ
      (1 : Matrix T T ℂ)))

omit [Fintype S] in
theorem one_kronecker_sum_kronecker_one {ι : Type*} (s : Finset ι) (M : ι → Matrix S S ℂ) :
    (1 : Matrix Unit Unit ℂ) ⊗ₖ ((∑ i ∈ s, M i) ⊗ₖ (1 : Matrix T T ℂ)) =
      ∑ i ∈ s, (1 : Matrix Unit Unit ℂ) ⊗ₖ (M i ⊗ₖ (1 : Matrix T T ℂ)) := by
  ext a b
  simp [kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul, Finset.mul_sum]

theorem sum_sideKraus (j : P) :
    ∑ rs, (g.sideKraus T j rs)ᴴ * g.sideKraus T j rs = 1 := by
  have hterm : ∀ rs : Res j × S, (g.sideKraus T j rs)ᴴ * g.sideKraus T j rs =
      (if (g.trans j rs.2).1 = rs.1 then (1 : ℂ) else 0) •
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ (Matrix.single rs.2 rs.2 (1 : ℂ) ⊗ₖ (1 : Matrix T T ℂ))) := by
    intro rs
    rw [sideKraus, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      conjTranspose_kronecker, conjTranspose_kronecker, conjTranspose_one, conjTranspose_one,
      conjTranspose_single, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul,
      Matrix.one_mul, single_mul_single_same]
    congr 1
    · split_ifs <;> simp
    · simp
  simp only [hterm]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [← one_kronecker_sum_kronecker_one, sum_single_one, one_kronecker_one, one_kronecker_one]

/-- The side port `j`: the Kraus family of `sideKraus`. -/
noncomputable def sideStep (j : P) : SubInstrument (Unit × (S × T)) (Unit × (S × T)) (Res j × S) :=
  SubInstrument.ofKraus (g.sideKraus T j) (g.sum_sideKraus T j)

theorem sideStep_branch (j : P) (rs : Res j × S) :
    (g.sideStep T j).branch rs = MatrixMap.conj (g.sideKraus T j rs) :=
  rfl

/-- A side port commutes with any operator on the table register. -/
theorem sideKraus_mul_one_kronecker {T' : Type} [Fintype T'] [DecidableEq T'] (R : Matrix T' T ℂ)
    (j : P) (rs : Res j × S) :
    g.sideKraus T' j rs * ((1 : Matrix Unit Unit ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ R)) =
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ R)) * g.sideKraus T j rs := by
  rw [sideKraus, sideKraus, Matrix.smul_mul, Matrix.mul_smul, ← mul_kronecker_mul,
    ← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul]
  simp only [Matrix.one_mul, Matrix.mul_one]

end side

/-! ## The runtimes -/

/-- The value of the hash at `x` in side state `s`, from a function `f` for the inputs that are not
overridden. -/
def answer (s : S) (f : X → Y) (x : X) : Y :=
  (g.ov s x).getD (f x)

/-- The runtime of a table register `T` read by `read`. -/
@[reducible]
noncomputable def tabRuntime (T : Type) [Fintype T] [DecidableEq T] (read : S × T → X → Y)
    (initT : SubState T) : QuantumRuntime (ovSpec X Y S P Res) where
  D := QReg.of (S × T)
  init := (SubState.basis g.init).prod initT
  step
    | .inl _ => SubInstrument.ofIsometry (tableOracle read) (conjTranspose_tableOracle_mul_self read)
    | .inr j => g.sideStep T j

/-- The game with the function `G` for the inputs that are not overridden. -/
@[reducible]
noncomputable def sampled (G : X → Y) : QuantumRuntime (ovSpec X Y S P Res) :=
  g.tabRuntime Unit (fun t ↦ g.answer t.1 G) (SubState.basis ())

variable [Nonempty Y]

/-- The game with the function held in uniform superposition. -/
@[reducible]
noncomputable def purified : QuantumRuntime (ovSpec X Y S P Res) :=
  g.tabRuntime (X → Y) (fun t ↦ g.answer t.1 t.2) (uniformFunctionState X Y)

/-- The read of a database with the overrides. -/
def readDb (t : S × Database X Y) (x : X) : Y :=
  g.answer t.1 (Database.lookup t.2) x

/-- The compression of every cell of the database register, beside the side state. -/
noncomputable abbrev compS : Matrix (S × Database X Y) (S × Database X Y) ℂ :=
  (1 : Matrix S S ℂ) ⊗ₖ compressAll X Y

theorem compS_mul_self : compS (S := S) (X := X) (Y := Y) * compS = 1 := by
  rw [compS, ← mul_kronecker_mul, Matrix.one_mul, compressAll_mul_self, one_kronecker_one]

theorem conjTranspose_compS : (compS (S := S) (X := X) (Y := Y))ᴴ = compS := by
  rw [compS, conjTranspose_kronecker, conjTranspose_one, conjTranspose_compressAll]

/-- The compressed oracle with the overrides. -/
noncomputable def compOracle :
    Matrix ((X × Y) × (S × Database X Y)) ((X × Y) × (S × Database X Y)) ℂ :=
  ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compS) * tableOracle g.readDb *
    ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compS)

theorem one_kronecker_compS_mul_self :
    ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compS (S := S) (X := X) (Y := Y)) *
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compS) = 1 := by
  rw [← mul_kronecker_mul, Matrix.one_mul, compS_mul_self, one_kronecker_one]

theorem conjTranspose_compOracle_mul_self : (g.compOracle)ᴴ * g.compOracle = 1 := by
  set A := (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compS (S := S) (X := X) (Y := Y)
  have hC : Aᴴ = A := by
    rw [conjTranspose_kronecker, conjTranspose_one, conjTranspose_compS]
  have hAA : A * A = 1 := one_kronecker_compS_mul_self
  rw [compOracle, conjTranspose_mul, conjTranspose_mul, hC]
  have h : A * (tableOracle g.readDb)ᴴ * A * (A * tableOracle g.readDb * A) =
      A * ((tableOracle g.readDb)ᴴ * (A * A) * tableOracle g.readDb) * A := by
    simp only [Matrix.mul_assoc]
  rw [show A * ((tableOracle g.readDb)ᴴ * A) * (A * tableOracle g.readDb * A) =
      A * (tableOracle g.readDb)ᴴ * A * (A * tableOracle g.readDb * A) by
    simp only [Matrix.mul_assoc], h, hAA, Matrix.mul_one, conjTranspose_tableOracle_mul_self,
    Matrix.mul_one, hAA]

/-- The game with the compressed oracle. -/
@[reducible]
noncomputable def compressed : QuantumRuntime (ovSpec X Y S P Res) where
  D := QReg.of (S × Database X Y)
  init := SubState.basis (g.init, Database.empty)
  step
    | .inl _ => SubInstrument.ofIsometry g.compOracle g.conjTranspose_compOracle_mul_self
    | .inr j => g.sideStep (Database X Y) j

end OvGame

end Qrom
