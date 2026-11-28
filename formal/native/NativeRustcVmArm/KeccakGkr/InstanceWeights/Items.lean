module

public import NativeRustcVmArm.KeccakGkr.InstanceWeights.Mask

/-!
# `instance_weights`: the `Buf` in the frame

When a block's writes pass `itemsOk` over the frame (region 0) whose powers' buffer holds `powers s
24`, the frame's `Buf<EW, 16>` at `616` holds the length `16` and `keccakInstanceWeights s`
(`buf_bytes`).
-/

namespace NativeRustcVmArm.KeccakGkr.InstanceWeights

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model LeanVM.Parameters

public section

theorem xorN_congr {f g : Nat → BitVec 64} (M : Nat) {n : Nat} (h : ∀ b < n, f b = g b) :
    xorN f M n = xorN g M n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [xorN, ih fun b hb ↦ h b (by omega), h n (by omega)]

/-- The bytes of the `Buf`: its length, then the weights. -/
@[expose] def bufBytes (s : EW) : List UInt8 :=
  NativeRustcVm.wordBytes 16 ++ (keccakInstanceWeights s).toList.flatMap NativeRustcVm.ewBytes

theorem iw_size (s : EW) : (keccakInstanceWeights s).size = 16 := by
  simp [keccakInstanceWeights, rmfeEmbedW, NativeVm.Equiv.rmfeEmbed_length]

theorem powers_size (b : EW) (n : Nat) : (powers b n).size = n := by
  unfold powers
  suffices ∀ (l : List Nat) (acc : Array EW × EW),
      (l.foldl (fun (acc : Array EW × EW) _ ↦ (acc.1.push acc.2, acc.2 * b)) acc).1.size =
        acc.1.size + l.length by
    rw [this]; simp
  intro l
  induction l with
  | nil => intro acc; simp
  | cons x l ih => intro acc; rw [List.foldl_cons, ih]; simp; omega

theorem bufBytes_length (s : EW) : (bufBytes s).length = 264 := by
  simp [bufBytes, NativeRustcVm.length_wordBytes, NativeRustcVm.length_ewBytes, iw_size]

/-- **The frame's `Buf`**: what a block passing `itemsOk` leaves at `616`, over the powers. -/
theorem buf_bytes [Labels] {st0 st : MachineData} {fb : BitVec 64} {S : SState}
    (hm : Match (Env.ofMachine st0 [(fb, 976)]) S st) (hok : itemsOk S.mem = true) {s : EW}
    (hpow : NativeRustcVm.EWsAt st0.dmem (fb + BitVec.ofNat 64 232) (powers s 24).toList) :
    NativeRustcVm.BytesAt st.dmem (fb + BitVec.ofNat 64 616) (bufBytes s) := by
  let env := Env.ofMachine st0 [(fb, 976)]
  have hsz : (powers s 24).size = 24 := powers_size s 24
  have hld : ∀ b < 24, env.load 0 (powOff + 16 * b + 0) 8 = ((powers s 24).getD b 0).c0.toBitVec ∧
      env.load 0 (powOff + 16 * b + 8) 8 = ((powers s 24).getD b 0).c1.toBitVec := by
    intro b hb
    have hb' : b < (powers s 24).toList.length := by rw [Array.length_toList, hsz]; exact hb
    have h := NativeRustcVm.EWsAt.getElem hpow hb'
    rw [NativeRustcVm.addr_add_add] at h
    obtain ⟨h1, h2⟩ := load_ew (env := env) (r := 0) (o := 232 + 16 * b) h
    rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, List.getElem?_eq_getElem hb',
      Option.getD_some]
    rw [show powOff + 16 * b + 0 = 232 + 16 * b from rfl, show powOff + 16 * b + 8 = 232 + 16 * b + 8
      from rfl]
    exact ⟨h1, h2⟩
  simp only [itemsOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hok
  obtain ⟨h16, hitems⟩ := hok
  have hlen : NativeRustcVm.WordAt st.dmem (fb + BitVec.ofNat 64 616) 16 := by
    have h := Sumcheck.Match.wordAt_write hm (r := 0) (o := 616) (v := .lit 16) rfl (by decide)
      (wordW_findWrite (lenOk_eq h16))
    rwa [show UInt64.ofBitVec (Sym.eval (Env.ofMachine st0 [(fb, 976)]) (.lit 16)) = 16 from rfl] at h
  have hword : ∀ e < 16, ∀ d < 2, ∀ x : UInt64,
      (∀ v, symMask (8 * d) v = some (iwMask e) →
        v.eval env = x.toBitVec) →
      NativeRustcVm.WordAt st.dmem (fb + BitVec.ofNat 64 (624 + 16 * e + 8 * d)) x := by
    intro e he d hd x hx
    obtain ⟨v, heq, hv⟩ := wordOk_eq (hitems e he d hd)
    have hw := Sumcheck.Match.wordAt_write hm (r := 0) rfl (by omega) (wordW_findWrite heq)
    rwa [hx v hv, UInt64.ofBitVec_toBitVec] at hw
  have hel : ∀ e < 16, NativeRustcVm.EWAt st.dmem (fb + BitVec.ofNat 64 624 + BitVec.ofNat 64 (16 * e))
      ((keccakInstanceWeights s).getD e 0) := by
    intro e he
    rw [NativeRustcVm.ewAt_iff, NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add]
    refine ⟨?_, ?_⟩
    · have := hword e he 0 (by decide) ((keccakInstanceWeights s).getD e 0).c0 fun v hv ↦ by
        rw [symMask_eval env 0 v _ hv, iw_word s he EW.c0 (fun _ _ ↦ rfl) rfl]
        exact xorN_congr _ fun b hb ↦ (hld b hb).1
      rwa [show 624 + 16 * e + 8 * 0 = 624 + 16 * e by omega] at this
    · have := hword e he 1 (by decide) ((keccakInstanceWeights s).getD e 0).c1 fun v hv ↦ by
        rw [symMask_eval env 8 v _ hv, iw_word s he EW.c1 (fun _ _ ↦ rfl) rfl]
        exact xorN_congr _ fun b hb ↦ (hld b hb).2
      rwa [show 624 + 16 * e + 8 * 1 = 624 + 16 * e + 8 by omega] at this
  unfold bufBytes
  rw [NativeRustcVm.bytesAt_append_iff]
  refine ⟨hlen, ?_⟩
  rw [show (NativeRustcVm.wordBytes 16).length = 8 from rfl, NativeRustcVm.addr_add_add]
  show NativeRustcVm.EWsAt _ _ _
  rw [NativeRustcVm.ewsAt_iff]
  intro i hi
  have hi' : i < 16 := by rw [Array.length_toList, iw_size] at hi; exact hi
  have := hel i hi'
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, List.getElem?_eq_getElem hi,
    Option.getD_some] at this
  rwa [show 616 + 8 = 624 from rfl]

end

end NativeRustcVmArm.KeccakGkr.InstanceWeights
