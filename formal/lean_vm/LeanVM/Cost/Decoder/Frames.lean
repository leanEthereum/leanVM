module

public import LeanVM.Cost.Decoder.Staged
public import LeanVM.Guest.Fast.Main

/-!
# The guest decoder's compiled chain: each callee's witness off its frame

The frame map keyed by the functions' indices (`Guest.Fast.NFrames`, `FunctionNames.lean`), and
each callee's witness a function of its call's words, the compiled readers (`Signatures.lean`,
`Da.lean`, `Hints.lean`) at the frame map's value: `xmssAtFrame` (`__loop2`, `fn_idx% main_loop2`,
the leanXMSS check inline there), `sphincsAtFrame` (`verify_sig_lean_sphincs`, and its three
`sp_wots` frames); neither is compiled here: the decoder's top looks their frames up once,
`xmssAtFrameT`, `sphincsAtFrameT`, `Top.lean`), `daAtFrame` (`da_verify`),
`proofAtFrame` (`verify_sub`), `hintsAtFrame` (`aggregate_claims`), each frame by `fn_idx%`
(`Guest/CoreRef.lean`). The signature
and proof readers read their tables off `R : ReaderTabs` (`Guest/Fast/Main.lean`), which the top
level builds once (`readerTabsC`) and passes.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main
open LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-! ## Each callee's witness off its frame, keyed by index -/

open LeanVM.Guest.Fast in
/-- The leanXMSS signature `__loop2`'s iteration on `args` checks (`fn_idx% main_loop2`: the check is
inline there), the readers' tables `R` given. -/
noncomputable def xmssAtFrame (R : ReaderTabs) (Vn : NFrames) (args : List E) :
    LeanXmss.Signature :=
  xmssSigOfA R.xmss (Vn (fn_idx% main_loop2) args [])

open LeanVM.Guest.Fast in
/-- The leanSPHINCS signature checked at slot address `p` (`verify_sig_lean_sphincs`), off
its frame and its three `sp_wots` frames, the readers' tables `R` given. -/
noncomputable def sphincsAtFrame (R : ReaderTabs) (σ : Val) (Vn : NFrames) (p : E) :
    Sphincs.Signature :=
  let s := Vn (fn_idx% verify_sig_lean_sphincs) [p, σ (.n 47)] []
  sphincsSigOfA R.sphincs s (Vn (fn_idx% sp_wots) (spWotsArgs s 0) (spWotsRets s 0))
    (Vn (fn_idx% sp_wots) (spWotsArgs s 1) (spWotsRets s 1)) (Vn (fn_idx% sp_wots) (spWotsArgs s 2) (spWotsRets s 2))

open LeanVM.Guest.Fast in
/-- The DA matrix `da_verify` checks on the call's words, the logarithm's tables `D`
given. -/
noncomputable def daAtFrame (D : LeanVM.Extraction.Fast.DiscreteLogTables) (Vn : NFrames)
    (args rets : List E) : LeanVM.Da.MatrixWitness :=
  dvWitND D (Vn (fn_idx% da_verify) args rets) Vn

open LeanVM.Guest.Fast in
/-- A child's proof at its `verify_sub` call's words, the readers' tables `R` given. -/
noncomputable def proofAtFrame (R : ReaderTabs) (rd : Reader) (Vn : NFrames) (cl : E → E → ℕ)
    (args : List E) : LeanVM.Protocol.Compile.Proof :=
  vsPiOfA R.whir rd (Vn (fn_idx% verify_sub) args []) Vn cl

open LeanVM.Guest.Fast in
/-- The batching's hints at `aggregate_claims`' call's words. -/
noncomputable def hintsAtFrame (rd : Reader) (Vn : NFrames) (args : List E) : BatchingHints :=
  aggHints rd (Vn (fn_idx% aggregate_claims) args [])

cost_enc LeanVM.Guest.Fast.ReaderTabs

-- the readers' tables, built: called once by the decoder's top level
cost_compile readerTabsC := LeanVM.Guest.Fast.readerTabs
cost_compile daAtFrameC := daAtFrame
cost_compile proofAtFrameC := proofAtFrame
cost_compile hintsAtFrameC := hintsAtFrame
end

end LeanVM.Cost.Decoder
