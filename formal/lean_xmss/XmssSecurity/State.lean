module

public import Statement.LeanXmss
public import EthLib.Cryptography.Proofs.LazyPermutation

/-!
# The Keccak state and the permutation's oracles, as leanVM and EthLib hold them

leanVM holds a Keccak state as a vector of its `25` lanes, EthLib as a structure of `25` fields,
lane `x + 5y` in both at the number `x + 5y`: the statement's two maps (`LeanXmss.stateToEthLib`,
`LeanXmss.stateOfEthLib`) are inverse, one bijection (`stateEquiv`). EthLib's oracles (coins, `π`
and `π⁻¹`) are leanVM's at the same lanes (`ethLibOracles`).
-/

@[expose] public section

namespace XmssSecurity

open LeanVM.Semantics (KeccakState)
open LeanXmss (stateToEthLib stateOfEthLib)

/-- leanVM's layout, carried to EthLib's and back, is unchanged. -/
theorem stateOfEthLib_stateToEthLib (s : KeccakState) : stateOfEthLib (stateToEthLib s) = s := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

/-- EthLib's layout, carried to leanVM's and back, is unchanged. -/
theorem stateToEthLib_stateOfEthLib (s : EthLib.Cryptography.Hash.Keccak.State) :
    stateToEthLib (stateOfEthLib s) = s := by
  cases s
  rfl

/-- **The two layouts of the Keccak state**: leanVM's as EthLib's. -/
def stateEquiv : KeccakState ≃ EthLib.Cryptography.Hash.Keccak.State :=
  ⟨stateToEthLib, stateOfEthLib, stateOfEthLib_stateToEthLib, stateToEthLib_stateOfEthLib⟩

open OracleComp OracleSpec Common
open EthLib.Cryptography.LazyPermutation (PermSpec)
open EthLib.Cryptography.Hash.Keccak (State)

/-- EthLib's oracles answered by leanVM's: a coin by a coin, `π` and `π⁻¹` at a state by leanVM's
at the same lanes. -/
def ethLibOracles : QueryImpl (unifSpec + PermSpec State) (OracleComp RandomPermutationOracles)
  | .inl n => liftM (RandomPermutationOracles.query (.inl n))
  | .inr (.inl s) => stateEquiv <$>
      liftM (RandomPermutationOracles.query (.inr (.forward (stateEquiv.symm s))))
  | .inr (.inr s) => stateEquiv <$>
      liftM (RandomPermutationOracles.query (.inr (.inverse (stateEquiv.symm s))))

end XmssSecurity

end
