module

public import XmssSecurity.Statement

@[expose] public section

namespace XmssSecurity

inductive AttackerAction where
  | hash (input : HashInput)
  | sign (request : SignRequest) (signature : Option Signature)
deriving DecidableEq

abbrev AttackerActionTrace := List AttackerAction

end XmssSecurity
