/-
  LeanVM.Guest.B1.Bits.QueryWindowsAtAll

  `decode_query_windows` complete placed at each of its 18 specializations.
-/

module

public import LeanVM.Guest.B1.Bits.QueryWindowsAt
public import LeanVM.Guest.B1.Bits.QueryWindowsData

/-!
# `decode_query_windows`, placed, every specialization

`qwDecodeAtD_holds`: for certificates whose frame runs fit their frames (`Lift.RunsFit`) with
their cells consecutive (`RunsConsec`), on memories defined below `2^k`, `7 ≤ k` (the range
checks), each deployed `(name, depth, cap depth)` is `QwDecodeAtD`: its template
(`queryWindows_data`) at a shape the generic proof covers (`qwShape_all`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Guest.Core

@[expose] public section

theorem qwDecodeAtD_holds {fs : String → ℕ} {cert : String → V → ℕ} (hfit : Lift.RunsFit fs cert)
    (hcons : RunsConsec cert) {k : ℕ} (hk : 7 ≤ k) :
    ∀ p ∈ queryWindowsShapes, QwDecodeAtD fs cert k p.2.1 p.2.2 p.1 :=
  fun p hp ↦ qwDecodeAtD_of hfit hcons (qwShape_all p hp) (queryWindows_data p hp) hk

end
end LeanVM.Guest.B1
