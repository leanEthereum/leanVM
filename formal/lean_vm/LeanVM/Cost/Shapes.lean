module

public import EthLib.Cryptography.Hash.Keccak

/-!
# Shapes of leanXMSS's values for the cost compiler

EthLib's leanXMSS values are encoded as numbers (two lanes) and as arrays (a signature's two
layers), not field by field. A compiled reader builds them with `lanes2OfFin` and `sigOf2`
(`Rule.lanes2OfFin`, `Rule.sigOf2`). -/

@[expose] public section

namespace LeanVM.Cost

/-- Two lanes from the number they make. -/
def lanes2OfFin (i : Fin (2 ^ 128)) : EthLib.Cryptography.Hash.Keccak.Lanes2 :=
  ⟨i.val.toUInt64, (i.val / 2 ^ 64).toUInt64⟩

/-- A structure of a value and its two layers' values, from the value and the function of the
two layers. -/
def sigOf2 {I Λ γ : Type} (mk : I → Λ → Λ → γ) (i : I) (ls : Fin 2 → Λ) : γ := mk i (ls 0) (ls 1)

end LeanVM.Cost
