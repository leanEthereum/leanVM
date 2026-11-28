/-
  LeanVM.Guest.B1.VsC.QwCertB2C

  The compiled frames lay out every `decode_query_windows`' `wins` run as `QwCert` asks.
-/

module

public import LeanVM.Guest.B1.VsC.QwA
public import LeanVM.Guest.B2C.Table

/-!
# `decode_query_windows`' frame layout, at the compiled frames

`qwCert_b2c`: for each deployed specialization, `B2C.cert` puts the `wins` run's values
`5 ..< 5 + qwW` on consecutive cells past the header, inside `B2C.fs`'s frame (one kernel
decision an entry). `qwA_b2c`: every specialization completes placed on the compiled frames.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

theorem qwCert_0 : QwCert B2C.fs B2C.cert "decode_query_windows__L9_L3" 9 3 := by
  unfold QwCert; decide +kernel

theorem qwCert_1 : QwCert B2C.fs B2C.cert "decode_query_windows__L10_L4" 10 4 := by
  unfold QwCert; decide +kernel

theorem qwCert_2 : QwCert B2C.fs B2C.cert "decode_query_windows__L11_L5" 11 5 := by
  unfold QwCert; decide +kernel

theorem qwCert_3 : QwCert B2C.fs B2C.cert "decode_query_windows__L12_L6" 12 6 := by
  unfold QwCert; decide +kernel

theorem qwCert_4 : QwCert B2C.fs B2C.cert "decode_query_windows__L13_L7" 13 7 := by
  unfold QwCert; decide +kernel

theorem qwCert_5 : QwCert B2C.fs B2C.cert "decode_query_windows__L14_L2" 14 2 := by
  unfold QwCert; decide +kernel

theorem qwCert_6 : QwCert B2C.fs B2C.cert "decode_query_windows__L14_L8" 14 8 := by
  unfold QwCert; decide +kernel

theorem qwCert_7 : QwCert B2C.fs B2C.cert "decode_query_windows__L15_L3" 15 3 := by
  unfold QwCert; decide +kernel

theorem qwCert_8 : QwCert B2C.fs B2C.cert "decode_query_windows__L16_L4" 16 4 := by
  unfold QwCert; decide +kernel

theorem qwCert_9 : QwCert B2C.fs B2C.cert "decode_query_windows__L17_L5" 17 5 := by
  unfold QwCert; decide +kernel

theorem qwCert_10 : QwCert B2C.fs B2C.cert "decode_query_windows__L18_L6" 18 6 := by
  unfold QwCert; decide +kernel

theorem qwCert_11 : QwCert B2C.fs B2C.cert "decode_query_windows__L19_L7" 19 7 := by
  unfold QwCert; decide +kernel

theorem qwCert_12 : QwCert B2C.fs B2C.cert "decode_query_windows__L20_L2" 20 2 := by
  unfold QwCert; decide +kernel

theorem qwCert_13 : QwCert B2C.fs B2C.cert "decode_query_windows__L20_L8" 20 8 := by
  unfold QwCert; decide +kernel

theorem qwCert_14 : QwCert B2C.fs B2C.cert "decode_query_windows__L21_L3" 21 3 := by
  unfold QwCert; decide +kernel

theorem qwCert_15 : QwCert B2C.fs B2C.cert "decode_query_windows__L22_L4" 22 4 := by
  unfold QwCert; decide +kernel

theorem qwCert_16 : QwCert B2C.fs B2C.cert "decode_query_windows__L23_L5" 23 5 := by
  unfold QwCert; decide +kernel

theorem qwCert_17 : QwCert B2C.fs B2C.cert "decode_query_windows__L24_L6" 24 6 := by
  unfold QwCert; decide +kernel

theorem qwCert_18 : QwCert B2C.fs B2C.cert "decode_query_windows__L25_L7" 25 7 := by
  unfold QwCert; decide +kernel

theorem qwCert_19 : QwCert B2C.fs B2C.cert "decode_query_windows__L26_L2" 26 2 := by
  unfold QwCert; decide +kernel

theorem qwCert_20 : QwCert B2C.fs B2C.cert "decode_query_windows__L27_L3" 27 3 := by
  unfold QwCert; decide +kernel

theorem qwCert_21 : QwCert B2C.fs B2C.cert "decode_query_windows__L28_L4" 28 4 := by
  unfold QwCert; decide +kernel

set_option maxRecDepth 100000 in
/-- **The compiled frames lay out every `wins` run.** -/
theorem qwCert_b2c : ∀ p ∈ queryWindowsShapes, QwCert B2C.fs B2C.cert p.1 p.2.1 p.2.2 :=
  List.forall_mem_cons.2 ⟨qwCert_0,
  List.forall_mem_cons.2 ⟨qwCert_1,
  List.forall_mem_cons.2 ⟨qwCert_2,
  List.forall_mem_cons.2 ⟨qwCert_3,
  List.forall_mem_cons.2 ⟨qwCert_4,
  List.forall_mem_cons.2 ⟨qwCert_5,
  List.forall_mem_cons.2 ⟨qwCert_6,
  List.forall_mem_cons.2 ⟨qwCert_7,
  List.forall_mem_cons.2 ⟨qwCert_8,
  List.forall_mem_cons.2 ⟨qwCert_9,
  List.forall_mem_cons.2 ⟨qwCert_10,
  List.forall_mem_cons.2 ⟨qwCert_11,
  List.forall_mem_cons.2 ⟨qwCert_12,
  List.forall_mem_cons.2 ⟨qwCert_13,
  List.forall_mem_cons.2 ⟨qwCert_14,
  List.forall_mem_cons.2 ⟨qwCert_15,
  List.forall_mem_cons.2 ⟨qwCert_16,
  List.forall_mem_cons.2 ⟨qwCert_17,
  List.forall_mem_cons.2 ⟨qwCert_18,
  List.forall_mem_cons.2 ⟨qwCert_19,
  List.forall_mem_cons.2 ⟨qwCert_20,
  List.forall_mem_cons.2 ⟨qwCert_21,
  List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- **Every `decode_query_windows` completes placed on the compiled frames.** -/
theorem qwA_b2c (al : String → Bool) (kd : ℕ) : ∀ p ∈ queryWindowsShapes,
    QwA B2C.fs al B2C.cert kd p.1 p.2.1 p.2.2 :=
  fun p hp => qwA_complete kd p hp (qwCert_b2c p hp)

end
end LeanVM.Guest.B1.VsC
