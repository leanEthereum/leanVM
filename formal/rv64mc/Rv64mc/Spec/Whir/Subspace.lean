/-
  Rv64mc.Spec.Whir.Subspace

  The contracts of `subspace_roots`, `Subspace::new`, `Subspace::at`, `novel_basis` and `novel_eval` (`whir.rs`), on
  `K` values as words (`kWords`). Each `Vec` result is written at `sret` (`a0`), fresh (`FreshVecW`):

  * `subspace_roots(log_n) -> Vec<K>` (`log_n` in `a1`): `Model.subspaceRootsRust`'s roots;
  * `Subspace::new(mu) -> Subspace` (`mu` in `a1`): `Model.SubspaceRust.new`'s two vectors (`SubspaceAt`);
  * `Subspace::at(&self, x: K) -> Vec<K>` (`self` in `a1`, `x` in `a2`): `Model.SubspaceRust.at`'s values;
  * `novel_basis(what: &[K], count) -> Vec<K>` (`what` in `a1`, `a2`, `count` in `a3`): `Model.novelBasisRust`'s
    basis wherever it has one (`assert!` does not return otherwise);
  * `novel_eval(coefficients: &[E], what: &[K]) -> E` (slices in `a0`..`a3`, the result's limbs in `a0`, `a1`):
    `Model.novelEvalRust`'s value.

  Fewer than `64` variables throughout (`K(1 << i)` wraps past `63`; every level has at most `30`).
-/

import Rv64mc.Spec.Whir.Basic
import Rv64mc.Model.Whir

namespace Rv64mc.Spec.Whir.Subspace

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

/-! ## `subspace_roots` -/

def RootsPre (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.Vec.byteSize ∧ (regs .x11).toNat < 64

def RootsPost (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  ∀ roots, Model.subspaceRootsRust (regs .x11).toNat = some roots → FreshVecW env m m' (regs .x10) (kWords roots)

/-- **The contract of `subspace_roots`**, function `i` of `p` with `need` bytes of stack. -/
def rootsSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (RootsPre env) (RootsPost env) (SretOut Layouts.Vec.byteSize)

/-! ## `Subspace` -/

/-- **The `Subspace` `s` at `a`**: its roots' and its inverses' `Vec`s, live. -/
def SubspaceAt (env : Env) (m : MachineState) (a : Word) (s : Model.SubspaceRust) : Prop :=
  WVecAt env m (a + BitVec.ofNat 64 Layouts.Subspace.roots) (kWords s.roots) ∧
    WVecAt env m (a + BitVec.ofNat 64 Layouts.Subspace.inverses) (kWords s.inverses)

/-- **A fresh `Subspace` `s` at `a`**: both `Vec`s allocated between `m` and `m'`. -/
def FreshSubspaceAt (env : Env) (m m' : MachineState) (a : Word) (s : Model.SubspaceRust) : Prop :=
  FreshVecW env m m' (a + BitVec.ofNat 64 Layouts.Subspace.roots) (kWords s.roots) ∧
    FreshVecW env m m' (a + BitVec.ofNat 64 Layouts.Subspace.inverses) (kWords s.inverses)

def NewPre (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.Subspace.byteSize ∧ (regs .x11).toNat < 64

def NewPost (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  ∀ s, Model.SubspaceRust.new (regs .x11).toNat = some s → FreshSubspaceAt env m m' (regs .x10) s

/-- **The contract of `Subspace::new`**, function `i` of `p` with `need` bytes of stack. -/
def newSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (NewPre env) (NewPost env) (SretOut Layouts.Subspace.byteSize)

def AtPre (env : Env) (s : Model.SubspaceRust) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.Vec.byteSize ∧ SubspaceAt env m (regs .x11) s

def AtPost (env : Env) (s : Model.SubspaceRust) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word)
    (m' : MachineState) : Prop :=
  FreshVecW env m m' (regs .x10) (kWords (s.at (BF64.ofBitVec (regs .x12))))

/-- **The contract of `Subspace::at`**, function `i` of `p` with `need` bytes of stack, for every subspace. -/
def atSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ s, Holds env p i need (AtPre env s) (AtPost env s) (SretOut Layouts.Vec.byteSize)

/-! ## `novel_basis`, `novel_eval` -/

/-- The `K` slice `ks` passed in `a`, `n`, its elements live. -/
def KSlice (env : Env) (m : MachineState) (a n : Word) (ks : List K) : Prop :=
  SliceArgs WordsAt m a n (kWords ks) ∧ env.Live m a (Layouts.K.byteSize * ks.length)

def BasisPre (env : Env) (what : List K) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.Vec.byteSize ∧ KSlice env m (regs .x11) (regs .x12) what

def BasisPost (env : Env) (what : List K) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word)
    (m' : MachineState) : Prop :=
  ∀ b, Model.novelBasisRust what (regs .x13).toNat = some b → FreshVecW env m m' (regs .x10) (kWords b)

/-- **The contract of `novel_basis`**, function `i` of `p` with `need` bytes of stack, for every `what`. -/
def basisSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ what, Holds env p i need (BasisPre env what) (BasisPost env what) (SretOut Layouts.Vec.byteSize)

def EvalPre (env : Env) (cs : List E) (what : List K) (regs : Reg → Word) (m : MachineState) : Prop :=
  SliceArgs EListAt m (regs .x10) (regs .x11) (cs.map Model.limbs) ∧
    env.Live m (regs .x10) (Layouts.E.byteSize * cs.length) ∧ KSlice env m (regs .x12) (regs .x13) what

def EvalPost (cs : List E) (what : List K) (_regs : Reg → Word) (_m : MachineState) (r' : Reg → Word)
    (_m' : MachineState) : Prop :=
  ∀ v, Model.novelEvalRust cs what = some v → r' .x10 = (Model.limbs v).1 ∧ r' .x11 = (Model.limbs v).2

/-- **The contract of `novel_eval`**, function `i` of `p` with `need` bytes of stack, for every two slices. -/
def evalSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ cs what, Holds env p i need (EvalPre env cs what) (EvalPost cs what)

end Rv64mc.Spec.Whir.Subspace
