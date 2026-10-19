/-
  LeanVM.Guest.B1.Tables.VerifyTablesSound

  `verify_tables` is sound (`SoundTables`), its four specification pieces discharged.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTables
public import LeanVM.Guest.B1.Tables.VerifyTablesSpecCe
public import LeanVM.Guest.B1.Tables.VerifyTablesSpecBus

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- **`verify_tables` is sound** on any memory image of at most `2^32` words. -/
theorem verify_tables_sound {κ : ℕ} (hκ : κ ≤ 32) (Lm : MemImage κ) {bytecode : List K}
    (hb : bytecode.length = 2 ^ 22) : SoundTables bytecode TCtx Lm.read :=
  verify_tables_sound_of (fun t ρ χ xi hxi => ceEx_eval t ρ χ xi hxi)
    (fun hsh => pushTotalEx_eval hsh) (fun hsh => pullTotalEx_eval hsh)
    (fun hsh => countTotalEx_eval hsh) hκ Lm hb

end
end LeanVM.Guest.B1.VerifySub
