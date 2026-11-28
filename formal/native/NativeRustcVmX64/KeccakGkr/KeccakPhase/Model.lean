module

public import NativeRustcVmX64.KeccakGkr.KeccakPhase.Exec
public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Areas

/-!
# `keccak_phase`: the model and the values the code computes

`keccakPhase` is `verifyKeccak` of `KECCAK`'s point and the output lanes `lanes` (`keccakPhase_eq`).
From the values' count `v` (`40 ≤ v ≤ 92`), the code's lane count and `memcpy`'s source and byte
count (`chain`); the lanes after `memcpy` copied the present ones over the zeros (`lanes_at`).
-/

namespace NativeRustcVmX64.KeccakGkr.KeccakPhase

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- The output lanes `keccak_phase` passes: `values`' from `keccakOut` on, zeros past its end. -/
def lanes (values : Array EW) : Array EW :=
  (Array.range 25).map fun lane ↦ values.getD (keccakOut + lane) 0

end

public section

theorem keccakOut_eq : keccakOut = 40 := by decide +kernel

theorem opKeccak_eq : opKeccak = 5 := by decide +kernel

/-- **`keccakPhase`** is `verifyKeccak` of `KECCAK`'s point and output lanes. -/
theorem keccakPhase_eq (layout : LayoutW) (evals : Array (Array EW × Array EW)) :
    NativeVm.Model.keccakPhase layout evals =
      NativeVm.Model.verifyKeccak (layout.tableLogHeights.getD opKeccak 0) (evals.getD opKeccak (#[], #[])).1
        (lanes (evals.getD opKeccak (#[], #[])).2) := by
  unfold NativeVm.Model.keccakPhase lanes
  generalize evals.getD opKeccak (#[], #[]) = e
  rcases e with ⟨p, v⟩
  rfl

theorem lanes_size (values : Array EW) : (lanes values).size = 25 := by simp [lanes]

theorem lanes_getElem (values : Array EW) {i : Nat} (hi : i < (lanes values).size) :
    (lanes values)[i] = values.getD (40 + i) 0 := by
  simp [lanes, keccakOut_eq]

/-- Bytes `memcpy` copied. -/
theorem bytes_copy {d d' : DataMem} {src dst : BitVec 64} {n o : Nat} {bs : List UInt8}
    (h : NativeRustcVm.BytesAt d (src + BitVec.ofNat 64 o) bs)
    (hc : NativeRustcVm.BytesAt d' dst (NativeRustcX64.bytesOf d src n)) (hle : o + bs.length ≤ n) :
    NativeRustcVm.BytesAt d' (dst + BitVec.ofNat 64 o) bs := by
  intro i hi
  have := hc (o + i) (by simp [NativeRustcX64.bytesOf]; omega)
  rw [NativeRustcVm.addr_add_add, this]
  simp only [NativeRustcX64.bytesOf, List.getElem_map, List.getElem_range]
  rw [← NativeRustcVm.addr_add_add, h i hi, Option.getD_some]

/-- **The output lanes** after `memcpy` copied the present ones over the zeros. -/
theorem lanes_at {d d' : DataMem} {fb0 vb : BitVec 64} {values : Array EW}
    (hfb : fb0.toNat + 400 ≤ 2 ^ 64)
    (hz : ∀ i < 50, NativeRustcVm.WordAt d (fb0 + BitVec.ofNat 64 (8 * i)) 0)
    (hv : NativeRustcVm.EWsAt d vb values.toList) (h40 : 40 ≤ values.size)
    (hc : NativeRustcVm.BytesAt d' fb0
      (NativeRustcX64.bytesOf d (vb + BitVec.ofNat 64 640) (16 * min (values.size - 40) 25)))
    (hs : NativeRustcVm.SameOutside d d'
      (NativeRustcVm.InRange fb0 (16 * min (values.size - 40) 25))) :
    NativeRustcVm.EWsAt d' fb0 (lanes values).toList := by
  refine NativeRustcVm.ewsAt_iff.mpr fun i hi ↦ ?_
  have hi' : i < 25 := by simpa [lanes_size] using hi
  rw [Array.getElem_toList, lanes_getElem]
  by_cases hp : i < min (values.size - 40) 25
  · have hlt : 40 + i < values.size := by omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, Option.getD_some]
    have h1 := hv.getElem (i := 40 + i) (by simpa using hlt)
    rw [show 16 * (40 + i) = 640 + 16 * i by omega, ← NativeRustcVm.addr_add_add] at h1
    exact bytes_copy (o := 16 * i) h1 hc
      (by rw [NativeRustcVm.length_ewBytes]; omega)
  · have hge : values.size ≤ 40 + i := by omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hge, Option.getD_none]
    have h0 : NativeRustcVm.EWAt d (fb0 + BitVec.ofNat 64 (16 * i)) 0 := by
      refine NativeRustcVm.ewAt_iff.mpr ⟨?_, ?_⟩
      · have := hz (2 * i) (by omega)
        rwa [show 8 * (2 * i) = 16 * i by omega] at this
      · have := hz (2 * i + 1) (by omega)
        rw [show 8 * (2 * i + 1) = 16 * i + 8 by omega, ← NativeRustcVm.addr_add_add] at this
        exact this
    refine NativeRustcVm.Layout.EWAt.of_same h0 (n := 16) ?_ le_rfl
    refine NativeRustcVm.Layout.Same.of_sameOutside hs fun j hj hq ↦ ?_
    rw [NativeRustcVm.addr_add_add, NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; omega),
      NativeRustcVm.toNat_add_ofNat (by omega)] at hq
    omega

/-! ## The code's values -/

section
variable [Labels] {env : Env}

omit [Labels] in
theorem ofInt_pos (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := BitVec.ofInt_natCast (w := 64) n

omit [Labels] in
theorem ult_iff (x y : BitVec 64) : x.ult y = decide (x.toNat < y.toNat) := by
  rw [BitVec.ult_eq_decide]

/-- **The values' count's consequences**: the lanes fit (`c0` false), `memcpy`'s source is lane
`KECCAK_OUT` of the values, its byte count the present lanes'. -/
theorem chain {v : Nat} (hl : (lenS.eval env).toNat = v) (h40 : 40 ≤ v) (h93 : v < 93) :
    c0.eval env = false ∧ srcS.eval env = env.base 1 + BitVec.ofNat 64 10976 ∧
      (nS.eval env).toNat = 16 * min (v - 40) 25 := by
  generalize hx : lenS.eval env = x at hl
  have hb : (bxS.eval env) = x := by
    simp only [bxS, Sym.eval, SBool.eval, CmpOp.apply, low_W64, hx, ult_iff]
    have hc : (decide (x.toNat < (93#64).toNat) = true) := by simp [hl]; omega
    simp only [hc, ↓reduceIte]
  have hs : (subS.eval env).toNat = v - 40 := by
    simp only [subS, Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, hb, ult_iff]
    have hc : (decide (x.toNat < (40#64).toNat) = true) = False := by simp [hl]; omega
    simp only [hc, ↓reduceIte]
    rw [BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    omega
  have hr15 : (r15S.eval env).toNat = min (v - 40) 25 := by
    simp only [r15S, Sym.eval, SBool.eval, CmpOp.apply, low_W64, ult_iff]
    split <;> rename_i h <;> simp only [decide_eq_true_eq, BitVec.toNat_ofNat] at h ⊢ <;> omega
  have hr10 : (r10S.eval env).toNat = 40 + min (v - 40) 25 := by
    simp only [r10S, Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, ult_iff]
    split <;> rename_i h <;> simp only [decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.toNat_add] at h ⊢ <;> omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [c0, SBool.eval, CmpOp.apply, low_W64, ult_iff, hb]
    have : ¬ (r10S.eval env).toNat > x.toNat := by rw [hr10, hl]; omega
    simp only [Bool.and_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq, beq_iff_eq]
    by_cases h : (r10S.eval env).toNat < x.toNat
    · exact Or.inl h
    · exact Or.inr (BitVec.eq_of_toNat_eq (by omega))
  · simp only [srcS, Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, hx, ult_iff]
    have hc : ((!decide (x.toNat < (93#64).toNat)) = true) = False := by simp [hl]; omega
    simp only [hc, ↓reduceIte]
    rw [show ((10336 : Int)) = ((10336 : Nat) : Int) from rfl,
      ofInt_pos, BitVec.add_comm, BitVec.add_assoc, ← BitVec.ofNat_add]
  · simp only [nS, Sym.eval, BinOp.apply, low_W64, ext_W64]
    have hsc : shiftCount .W64 (BitVec.ofNat 64 4) = 4 := by decide
    rw [hsc, BitVec.toNat_shiftLeft, hr15, Nat.shiftLeft_eq]
    omega

/-- **The point's slice**: its items and its count, at most `30`. -/
theorem inst_eval {n : Nat} (hl : (ptS.eval env).toNat = n) (h : n ≤ 30) :
    instS.eval env = env.base 1 + BitVec.ofNat 64 9848 ∧ (nInstS.eval env).toNat = n := by
  generalize hx : ptS.eval env = x at hl
  constructor
  · simp only [instS, Sym.eval, SBool.eval, CmpOp.apply, low_W64, hx, ult_iff]
    have hc : ((!decide (x.toNat < (31#64).toNat)) = true) = False := by simp [hl]; omega
    simp only [hc, ↓reduceIte]
    rw [show ((9848 : Int)) = ((9848 : Nat) : Int) from rfl, ofInt_pos]
  · simp only [nInstS, Sym.eval, SBool.eval, CmpOp.apply, low_W64, hx, ult_iff]
    have hc : (decide (x.toNat < (31#64).toNat) = true) := by simp [hl]; omega
    simp only [hc, ↓reduceIte]
    exact hl

end

end

end NativeRustcVmX64.KeccakGkr.KeccakPhase
