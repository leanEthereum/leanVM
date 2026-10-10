import Lake
open Lake DSL

/-!
The leanXMSS guest's verification against the Ethereum XMSS specification.

* `EthCryptographySpecs`: the specification's `Xmss` modules, vendored verbatim (see `scripts/check-spec.sh`).
* `Leanxmss`: the guest library as Charon and Aeneas translate it, and the models of the SDK functions it calls.
* `LeanxmssProofs`: the proofs.
-/

require aeneas from git "https://github.com/AeneasVerif/aeneas" @ "aa66752b15d02335f936f607b5ad5b9fecb65b13" / "backends/lean"

package «leanxmss-verification»

lean_lib «EthCryptographySpecs» where
  srcDir := "Spec"
  roots := #[`EthCryptographySpecs.Xmss]

lean_lib «Leanxmss»

@[default_target]
lean_lib «LeanxmssProofs»
