module

public import Quantum.StdModel.Props.Prf
public import Quantum.StdModel.Props.Tcr
public import Quantum.StdModel.Props.Cpre
public import Quantum.StdModel.Props.EncTcr
public import Quantum.StdModel.Props.Itsr

/-!
# The properties of Keccak-256 in the standard-model reduction

The property games of the design (D1 to D6), each against quantum adversaries with superposition
access to an oracle world's hash and classical access to the challenger:

* `Props.Prf`: KIM-PRF (`kimPrfAdv`, `derivedKimFn`) and PRF_msg (`prfMsgAdv`).
* `Props.Tcr`: SM-TCR-C (`smTcr`).
* `Props.Cpre`: chain preimage resistance with adaptive or selective openings (`cpre`).
* `Props.EncTcr`: EncTCR$ (`encTcrSalt`) and EncTCR+C (`encTcrCtr`).
* `Props.Itsr`: ITSR of the message hash (`itsr`).
-/
