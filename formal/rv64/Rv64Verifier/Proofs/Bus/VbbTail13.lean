import Rv64Verifier.Proofs.Bus.VbbTail12

/-!
# `verify_bus_balance` past the GKR loop: the claims' `Vec` as it fills

`ClaimsOk` is `ClaimsAt` with every claim's point buffer apart from the claims' buffer, so that
writing the next claim (`push`) keeps the others. It keeps across a step writing the frame
(`keepR`) and across `grow_one` (`grow`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript

/-- A claim from a `Vec` in registers written at `a`. -/
theorem NewVecR.claimAt {s t : MachineState} {a cap ptr len : Word} {xs : List E}
    (h : NewVecR s t cap ptr len xs) (hlo : heapStart ≤ heapNext s) (e0 : t.getMem a = cap)
    (e8 : t.getMem (a + 8) = ptr) (e16 : t.getMem (a + 16) = len) {col : Nat}
    (ec : (t.getMem (a + 24)).toNat = col) {x : E} (ex : eAt t (a + 32) = x) :
    ClaimAt s t a ⟨col, xs, x⟩ := by
  have hb := h.buf
  have hle := h.le
  have hel := h.elems
  simp only [NewBuf] at hb
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ec, ex⟩
  · simp only [RawVecOk, Buf, vecPtr, vecCap, e0, e8]
    exact ⟨hb.1, hb.2.imp_right fun h' ↦ ⟨by omega, h'.2⟩⟩
  · simp only [vecLen, vecCap, e0, e16]; exact hle
  · simp only [NewBuf, vecPtr, vecCap, e0, e8]; exact hb
  · simp only [vecEs, vecPtr, vecLen, e8, e16]; exact hel

/-- A claim whose 56 bytes and point buffer a step misses. -/
theorem ClaimAt.keepD {s v w : MachineState} {B : Word → Prop} {a : Word} {c : ColumnClaim}
    (h : ClaimAt s v a c) (fr : DFrame v w B) (hm : heapNext v ≤ heapNext w)
    (ha : a.toNat + 56 ≤ 2 ^ 64) (hhdr : ∀ y, Within y a 56 → ¬ B y)
    (hbuf : ∀ y, Within y (vecPtr v a) ((vecCap v a).toNat * 24) → ¬ B y) : ClaimAt s w a c := by
  have hw (j : Nat) (hj : j + 8 ≤ 56) : w.getMem (a + BitVec.ofNat 64 j) =
      v.getMem (a + BitVec.ofNat 64 j) :=
    fr _ fun i hi ↦ hhdr _ (by addr_omega [ha, hi, hj])
  obtain ⟨hl, hb⟩ := h.vec.bound
  have hbd : (vecPtr v a).toNat + (vecCap v a).toNat * 24 ≤ 2 ^ 64 := by
    simp only [NewBuf, heapNext] at hb
    rcases hb.2 with h0 | ⟨b1, b2⟩
    · omega
    · have := (v.getMem nextAddr).isLt; omega
  refine ⟨h.vec.transfer (by simpa using hw 0 (by omega)) (hw 8 (by omega)) (hw 16 (by omega)) hm
    (eListAt_congr fun i hi ↦ ?_), ?_, ?_⟩
  · have bw (j : Nat) (hj : j + 8 ≤ 24) : w.getMem (vecPtr v a + BitVec.ofNat 64 (24 * i) +
        BitVec.ofNat 64 j) = v.getMem (vecPtr v a + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 j) :=
      fr _ fun k hk ↦ hbuf _ (by addr_omega [hbd, hi, hl, hj, hk])
    exact eAt_congr (by simpa using bw 0 (by omega)) (bw 8 (by omega)) (bw 16 (by omega))
  · rw [show a + 24 = a + BitVec.ofNat 64 24 from rfl, hw 24 (by omega)]; exact h.column
  · rw [← h.value]
    have e40 : a + 32 + 8 = a + BitVec.ofNat 64 40 := by rw [BitVec.add_assoc]; rfl
    have e48 : a + 32 + 16 = a + BitVec.ofNat 64 48 := by rw [BitVec.add_assoc]; rfl
    exact eAt_congr (hw 32 (by omega)) (by rw [e40]; exact hw 40 (by omega))
      (by rw [e48]; exact hw 48 (by omega))

/-- The claims' `Vec`, every claim's point buffer apart from the claims' buffer. -/
structure ClaimsOk (s t : MachineState) (cap ptr len : Word) (cs : List ColumnClaim) : Prop where
  claims : ClaimsAt s t cap ptr len cs
  apart : ∀ i < len.toNat, Apart (vecPtr t (ptr + BitVec.ofNat 64 (56 * i)))
    ((vecCap t (ptr + BitVec.ofNat 64 (56 * i))).toNat * 24) ptr (56 * cap.toNat)

/-- The claims' buffer lies in the heap. -/
theorem ClaimsAt.inHeap {s t : MachineState} {cap ptr len : Word} {cs : List ColumnClaim}
    (hpre : BusBalancePre s) (h : ClaimsAt s t cap ptr len cs) (hh : HeapOk t) :
    56 * cap.toNat = 0 ∨ (0x20000000 ≤ ptr.toNat ∧ ptr.toNat + 56 * cap.toNat ≤ 0x78000000) := by
  have hb := h.buf
  have hlo := hpre.heap.lo
  have hhi := hh.hi
  simp only [NewBuf, heapNext, heapStart, heapEnd] at hb hlo hhi
  rcases hb.2 with h0 | ⟨b1, b2⟩
  · exact Or.inl h0
  · exact Or.inr ⟨by omega, by omega⟩

/-- Writing the next claim, apart from the others and their points, keeps them. -/
theorem ClaimsOk.push {s v w : MachineState} {A : Word → Prop} (hpre : BusBalancePre s)
    {cap ptr len len' : Word} {cs : List ColumnClaim} (h : ClaimsOk s v cap ptr len cs)
    (hv : HeapOk v) (hlt : len.toNat < cap.toNat)
    (fr : DFrame v w fun a ↦ A a ∨ Within a (ptr + BitVec.ofNat 64 (56 * len.toNat)) 56)
    (hA : FrameW s A) (hn : heapNext w = heapNext v) {c : ColumnClaim}
    (hc : ClaimAt s w (ptr + BitVec.ofNat 64 (56 * len.toNat)) c)
    (hca : Apart (vecPtr w (ptr + BitVec.ofNat 64 (56 * len.toNat)))
      ((vecCap w (ptr + BitVec.ofNat 64 (56 * len.toNat))).toNat * 24) ptr (56 * cap.toNat))
    (hl' : len'.toNat = len.toNat + 1) : ClaimsOk s w cap ptr len' (cs ++ [c]) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨C, ap⟩ := h
  have hle := C.le
  have hlen := C.len
  have hbuf := C.buf
  have hin := C.inHeap hpre hv
  have hcap : 0 < cap.toNat := by omega
  have hin' : 0x20000000 ≤ ptr.toNat ∧ ptr.toNat + 56 * cap.toNat ≤ 0x78000000 := by
    rcases hin with h0 | h0
    · omega
    · exact h0
  have keep (i : Nat) (hi : i < len.toNat) :
      ClaimAt s w (ptr + BitVec.ofNat 64 (56 * i)) (cs[i]'(by omega)) := by
    have Ci := C.claims i (by omega)
    have api := ap i hi
    refine Ci.keepD fr (by rw [hn]) (by addr_omega [hin', hi, hlt]) (fun y hy hB ↦ ?_)
      (fun y hy hB ↦ ?_)
    · rcases hB with hB | hB
      · have := hA y hB; addr_omega [this, hy, hin', hi, hlt, hb1]
      · addr_omega [hB, hy, hin', hi, hlt]
    · rcases hB with hB | hB
      · have := hA y hB
        have hpb := Ci.vec.buf
        simp only [NewBuf, heapNext] at hpb
        have hhi := hv.hi
        simp only [heapNext, heapEnd] at hhi
        rcases hpb.2 with h0 | ⟨b1, b2⟩
        · simp only [Within] at hy; omega
        · addr_omega [this, hy, b2, hhi, hb1]
      · simp only [Apart] at api
        addr_omega [hB, hy, hin', hi, hlt, api]
  refine ⟨⟨by omega, by simp only [NewBuf] at hbuf ⊢; rw [hn]; exact hbuf,
    by rw [hl', List.length_append, ← hlen]; rfl, fun i hi ↦ ?_⟩, fun i hi ↦ ?_⟩
  · rw [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_or_ge i cs.length with h1 | h1
    · rw [List.getElem_append_left h1]; exact keep i (by omega)
    · have hi' : i = len.toNat := by omega
      subst hi'
      have e : (cs ++ [c])[len.toNat]'(by simp; omega) = c := by
        rw [List.getElem_append_right (by omega)]; simp [hlen]
      rw [e]; exact hc
  · rcases Nat.lt_or_ge i len.toNat with h1 | h1
    · have K := keep i h1
      have hw (j : Nat) (hj : j + 8 ≤ 56) : w.getMem (ptr + BitVec.ofNat 64 (56 * i) +
          BitVec.ofNat 64 j) = v.getMem (ptr + BitVec.ofNat 64 (56 * i) + BitVec.ofNat 64 j) :=
        fr _ fun k hk hB ↦ by
          rcases hB with hB | hB
          · have := hA _ hB; addr_omega [this, hk, hin', h1, hlt, hb1, hj]
          · addr_omega [hB, hk, hin', h1, hlt, hj]
      have e0 := hw 0 (by omega)
      have e8 := hw 8 (by omega)
      rw [add_ofNat_zero] at e0
      simp only [vecPtr, vecCap, e0]
      rw [show ptr + BitVec.ofNat 64 (56 * i) + 8 =
        ptr + BitVec.ofNat 64 (56 * i) + BitVec.ofNat 64 8 from rfl, e8]
      exact ap i h1
    · have hi' : i = len.toNat := by omega
      subst hi'
      exact hca

/-- `ClaimsOk` keeps across a step writing the frame. -/
theorem ClaimsOk.keepR {s v w : MachineState} {A : Word → Prop} (hpre : BusBalancePre s)
    (st : StepR s v w A) (hA : FrameW s A) {cap ptr len : Word} {cs : List ColumnClaim}
    (h : ClaimsOk s v cap ptr len cs) : ClaimsOk s w cap ptr len cs := by
  obtain ⟨C, ap⟩ := h
  have hb := C.buf
  have hle := C.le
  refine ⟨C.keepR hpre st hA, fun i hi ↦ ?_⟩
  have hbd : ptr.toNat + 56 * cap.toNat ≤ 2 ^ 64 := by
    simp only [NewBuf] at hb
    rcases hb.2 with h0 | ⟨b1, b2⟩
    · omega
    · have := st.heap.hi
      simp only [heapNext, heapEnd] at *; omega
  have w0 := st.bufWord hpre hA hb (x := ptr + BitVec.ofNat 64 (56 * i))
    (by addr_omega [hbd, hi, hle]) (by addr_omega [hbd, hi, hle])
  have w8 := st.bufWord hpre hA hb (x := ptr + BitVec.ofNat 64 (56 * i) + 8)
    (by addr_omega [hbd, hi, hle]) (by addr_omega [hbd, hi, hle])
  simp only [vecPtr, vecCap, w0, w8]
  exact ap i hi

/-- `ClaimsOk` across `grow_one`: the claims' bytes copied to a buffer allocated after every
point. -/
theorem ClaimsOk.grow {s u v : MachineState} {A : Word → Prop} (hpre : BusBalancePre s)
    (st : StepR s u v A) (hA : FrameW s A) {cap ptr len cap' ptr' : Word}
    {cs : List ColumnClaim} (h : ClaimsOk s u cap ptr len cs) (hle : cap.toNat ≤ cap'.toNat)
    (hby : bytesAt v ptr' (cap.toNat * 56) = bytesAt u ptr (cap.toNat * 56))
    (hb : NewBuf u v ptr' (cap'.toNat * 56) 8) (hu : heapNext s ≤ heapNext u) :
    ClaimsOk s v cap' ptr' len cs := by
  obtain ⟨C, -⟩ := h
  have C' := C.grow hpre st hA hle hby hb hu
  refine ⟨C', fun i hi ↦ ?_⟩
  have hl := C.le
  have hlen := C.len
  have hpa : ptr'.toNat % 8 = 0 := hb.1
  have hqa : ptr.toNat % 8 = 0 := C.buf.1
  have wd (j : Nat) (hj : j + 8 ≤ 56) (hj8 : j % 8 = 0) :
      v.getMem (ptr' + BitVec.ofNat 64 (56 * i) + BitVec.ofNat 64 j) =
        u.getMem (ptr + BitVec.ofNat 64 (56 * i) + BitVec.ofNat 64 j) := by
    rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact getMem_eq_of_bytesAt hby hpa hqa (by omega) (by omega)
  have e0 := wd 0 (by omega) (by omega)
  rw [add_ofNat_zero, add_ofNat_zero] at e0
  have e8 := wd 8 (by omega) (by omega)
  simp only [vecPtr, vecCap, e0]
  rw [show ptr' + BitVec.ofNat 64 (56 * i) + 8 =
    ptr' + BitVec.ofNat 64 (56 * i) + BitVec.ofNat 64 8 from rfl, e8]
  have Ci := C.claims i (by omega)
  have hpb := Ci.vec.buf
  have hn := hb.2
  simp only [NewBuf, vecPtr, vecCap] at hpb
  simp only [Apart]
  rcases hpb.2 with h0 | ⟨b1, b2⟩
  · exact Or.inl h0
  · rcases hn with h0 | ⟨b3, b4⟩
    · exact Or.inr (Or.inl (by omega))
    · rw [show ptr + BitVec.ofNat 64 (56 * i) + BitVec.ofNat 64 8 =
        ptr + BitVec.ofNat 64 (56 * i) + 8 from rfl]
      exact Or.inr (Or.inr (Or.inl (by omega)))

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
