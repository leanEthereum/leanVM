import XmssSecurity.Proof.IdealStatement

namespace XmssSecurity

inductive AttackerAction where
  | hash (input : HashInput)
  | sign (request : SignRequest) (signature : Option Signature)
deriving DecidableEq

abbrev AttackerActionTrace := List AttackerAction

end XmssSecurity
