module

public import Quantum.Sphincs.HonestTable.Values
public import Quantum.Sphincs.HonestTable.Disclosure

@[expose] public section

/-!
# leanSPHINCS's honest table

leanSPHINCS's honest computations as functions of the table `L = (t, π, SK.seed)`
(`Quantum.Sphincs.HonestTable.Values`), and its value positions, slots and disclosures
(`Quantum.Sphincs.HonestTable.Disclosure`).

## Contract C1: value positions

Every later SPHINCS module names honest 128-bit values by `ValPos` and reads them by `valuePos L`:

* `ValPos.chain l τ e i j`, `j : Fin chainLength`: position `j` of chain `i` of the one-time key
  `(l, τ, e)`; `j = 0` is the chain start (the output of the secret `PRF` slot), `j = 3` the end.
* `ValPos.tree l τ level index`, `level ≤ 10`: the value of tree `τ` of layer `l` at `level`; level
  `0` is the one-time leaf of key `index`, levels `1` to `h_l` the nodes, level `h_l`, index `0` the
  root. `PK.root` is `rootPos = tpos topLayer 0 10 0`.
* `ValPos.forsSecret idx κ s`: the secret of leaf `s` of FORS tree `κ` of instance `idx`.
* `ValPos.forsTree idx κ height node`, `height ≤ 10`: the FORS leaf (height `0`, the hash of the
  secret), a FORS node, the FORS root (height `10`, node `0`).
* `ValPos.forsKey idx`: the FORS public key of instance `idx` (`T_k` of its 24 roots).
* `cpos`, `tpos`, `fpos`: the positions at natural indices, reduced into range;
  `valuePos_cpos`, `valuePos_tpos`, `valuePos_fpos`: in range, the table's `chainValue`,
  `treeValue`, `forsValue`.
* A WOTS+C key is `Key = Layer × TreeIndex × TreeLeafIndex`, `keyOf l idx = K_l(idx)`.
  `msgPos K` is the position of the one value `K` signs: the FORS key of instance `τ 2^8 + e` at
  the bottom, the root of tree `τ 2^(h_l) + e` of the layer below above it. `msgPos_eq`: in every
  signature of index `idx`, `K_l(idx)` signs `valuePos L (msgPos (keyOf l idx))`
  (`HonestTable.layerMessage`).
* Slots (`Quantum.Sphincs.Slot`): `InTable s` for the structural slots; `slotOutPos s` the position
  a structural or secret slot outputs; `slotNeed s` the positions its honest path depends on;
  `slotInput seed s f` its input from values `f` (structural and `H_msg` slots);
  `honestInput_eq_slotInput`, `honestInput_hmsg_eq_slotInput`: at `f = valuePos L` and
  `seed = L.publicSeed`, the honest input; `slotInput_congr`: the input depends on `f` only on
  `slotNeed s`; `target_eq_some`, `target_prf`: a structural or secret slot's digest is
  `valuePos L (slotOutPos s)`.

The hidden coordinates outside `ValPos` (the randomizers `R(M)`, the `H_msg` outputs, the digest
stream) belong to the template (contract C2).
-/

end
