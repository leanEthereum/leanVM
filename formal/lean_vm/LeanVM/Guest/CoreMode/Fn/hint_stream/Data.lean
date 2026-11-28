/-
  LeanVM.Guest.CoreMode.Fn.hint_stream.Data

  `hint_stream`'s own routing data (`CoreMode/FnReg.lean`): its caller, and the exponent bound of its chunk count
  `n_g`, which `verify_sub` range checks.
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber

namespace LeanVM.Guest.CoreMode.Own.hint_stream

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its caller** (`Res.callersG`): `verify_sub`, whose `stream_chunks` it gets as `n_g`. -/
def stCallers : List (String × String) := [(name% «hint_stream», name% «verify_sub»)]

/-- **Its exponent facts**: its chunk count `n_g` (its parameter `1`) is `g^e`, `e < 33`
(`verify_sub`'s `assert log(stream_chunks) < STREAM_CAP // STREAM_CHUNK + 1`). -/
def expFacts : List (String × ℕ × Option ℕ × ℕ) := [(name% «hint_stream», 1, none, 33)]

end

end LeanVM.Guest.CoreMode.Own.hint_stream
