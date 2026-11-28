module

public import NativeRustcVmArm.Wire.RdRows.Basic

/-!
# `rd_rows`' writes

A block's writes inside leaf `i` (a chunk of it, region 1 of `chEnv`): the frame kept
(`Frm.chunk`), the frame's own words kept (`frame_word`), the memory of the rows so far kept
(`Kept.chunk`), zeros written (`zero_word`, `zeros_snoc`) and kept (`zeros_chunk`).
-/

namespace NativeRustcVmArm.Wire.RdRows

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8}

/-- A byte of the frame is a byte of the stack. -/
theorem frame_in_stack (hst : StackOk m0 144) {o : Nat} (ho : o < 112) :
    InRange (base m0 144) 144 (base m0 112 + BitVec.ofNat 64 o) := by
  rw [← Ring.base_add (F := 112) (N := 144) (by omega) hst.2.1, NativeRustcVm.addr_add_add]
  exact NativeRustcVm.inRange_add (by omega) (by
    have := Ring.base_noWrap (m0 := m0) (F := 144) hst.2.1; unfold NoWrap at this; omega)

/-- A chunk of leaf `i` misses the frame. -/
theorem Geo.not_frame (G : Geo m0 bp B) {i o sz : Nat} (hi : i < nr m0) (ho : o + sz ≤ 512)
    (hsz : 0 < sz) {f : Nat} (hf : f < 112) :
    ¬InRange (leaf m0 i + BitVec.ofNat 64 o) sz (base m0 112 + BitVec.ofNat 64 f) := fun hq ↦
  G.g.wS _ (G.chunk_apart hi ho hsz hq).1 (frame_in_stack G.g.st hf)

/-- **The frame across a block writing a chunk of leaf `i`.** -/
theorem Frm.chunk [Labels] (G : Geo m0 bp B) {i o sz : Nat} (hi : i < nr m0) (ho : o + sz ≤ 512)
    (hsz : 0 < sz) {m m' : MachineData} {env : Env} {S S' : SState} (hfr : Frm m0 m)
    (hm : Match env S m) (hm' : Match env S' m') (hwf : env.WF) (hd : m.dmem = env.mem0)
    (hsp : S'.sp = S.sp)
    (hs : SameOutside m.dmem m'.dmem (InRange (leaf m0 i + BitVec.ofNat 64 o) sz)) :
    Frm m0 m' := by
  refine hfr.step (Match.sp_eq hm hm' hsp) (fun x hx ↦ absurd hx (by simp))
    (fun p hp ↦ hm'.kept hwf p (by rw [← hd]; exact hp)) hs
    (fun q hq ↦ .inr (.inr (G.chunk_apart hi ho hsz hq).1)) fun p hp j hj hq ↦ ?_
  have := (show ∀ p ∈ slots, p.1 + 8 ≤ 112 by decide) p hp
  rw [NativeRustcVm.addr_add_add (base m0 112)] at hq
  exact G.not_frame hi ho hsz (by omega) hq

/-- A word of the frame survives a write into a chunk of leaf `i`. -/
theorem Geo.frame_word (G : Geo m0 bp B) {i o sz : Nat} (hi : i < nr m0) (ho : o + sz ≤ 512)
    (hsz : 0 < sz) {d d' : Mem 64} (hs : SameOutside d d' (InRange (leaf m0 i + BitVec.ofNat 64 o) sz))
    {f : Nat} (hf : f + 8 ≤ 112) {w : UInt64} (h : WordAt d (base m0 112 + BitVec.ofNat 64 f) w) :
    WordAt d' (base m0 112 + BitVec.ofNat 64 f) w :=
  NativeRustcVm.BytesAt.of_sameOutside h hs fun j hj hq ↦ by
    rw [NativeRustcVm.length_wordBytes] at hj
    rw [NativeRustcVm.addr_add_add (base m0 112)] at hq
    exact G.not_frame hi ho hsz (by omega) hq

/-- Leaf `i` does not wrap. -/
theorem Geo.leaf_noWrap (G : Geo m0 bp B) {i : Nat} (hi : i < nr m0) : NoWrap (leaf m0 i) 512 := by
  have := G.leaf_toNat (i := i) (o := 0) (by omega)
  rw [NativeRustcVm.addr_add_zero] at this
  unfold NoWrap; rw [this]; have := G.lvNw; omega

/-- **The rows so far survive** a write into a chunk of leaf `i`. -/
theorem Kept.chunk (G : Geo m0 bp B) {c i ci : Nat} {rows : List (List K)} {d d' : Mem 64}
    (hk : Kept m0 bp B c i rows ci d) (hi : i < nr m0) {o sz : Nat} (ho : o + sz ≤ 512)
    (hsz : 0 < sz) (hs : SameOutside d d' (InRange (leaf m0 i + BitVec.ofNat 64 o) sz)) :
    Kept m0 bp B c i rows ci d' where
  hrows := hk.hrows
  hrd := G.g.reader_frame rfl hk.hrd
    (NativeRustcVm.SameOutside.mono hs fun q hq ↦ .inr (G.chunk_apart hi ho hsz hq).1)
  hlvs := by
    intro j hj
    obtain ⟨hl, hw⟩ := rdRows_length (B := B) _ _ hk.hrows
    simp only [List.length_map] at hj
    have hx := hk.hlvs j (by simpa using hj)
    have hlen : ((rows.map fun x ↦ paddedLeaf x (lw m0))[j]'(by simpa using hj)).length = lw m0 := by
      simp only [List.getElem_map, paddedLeaf, List.length_append, List.length_replicate]
      have := hw _ (List.getElem_mem hj)
      have := G.rwlw
      omega
    refine NativeRustcVm.BytesAt.of_sameOutside hx hs fun t ht hq ↦ ?_
    rw [NativeRustcVm.length_wordsBytes, List.length_map, hlen] at ht
    have h64 := G.lw64
    have := G.lvNw
    refine (G.chunk_apart hi ho hsz hq).2 ?_
    rw [NativeRustcVm.addr_add_add]
    exact NativeRustcVm.inRange_add (by omega) (by omega)

/-- The zeros so far survive a write after them. -/
theorem zeros_chunk (G : Geo m0 bp B) {i t o sz : Nat} (hi : i < nr m0) (ho : o + sz ≤ 512)
    (hto : 8 * t ≤ o) {d d' : Mem 64}
    (hs : SameOutside d d' (InRange (leaf m0 i + BitVec.ofNat 64 o) sz))
    (h : WordsAt d (leaf m0 i) (List.replicate t 0)) : WordsAt d' (leaf m0 i) (List.replicate t 0) :=
  NativeRustcVm.BytesAt.of_sameOutside h hs fun j hj ↦ by
    rw [NativeRustcVm.length_wordsBytes, List.length_replicate] at hj
    exact NativeRustcVm.not_inRange_sub (G.leaf_noWrap hi) ho (by omega) (.inl (by omega))

/-- One more zero. -/
theorem zeros_snoc {d : Mem 64} {a : BitVec 64} {t : Nat} (h : WordsAt d a (List.replicate t 0))
    (h0 : WordAt d (a + BitVec.ofNat 64 (8 * t)) 0) : WordsAt d a (List.replicate (t + 1) 0) := by
  rw [List.replicate_succ', NativeRustcVm.wordsAt_append_iff, List.length_replicate,
    NativeRustcVm.wordsAt_singleton_iff]
  exact ⟨h, h0⟩

/-- **A zero written** by a block (`str xzr` / `stp xzr, xzr`): the word at the write. -/
theorem zero_word [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r o sz : Nat} {b : BitVec 64} (hb : env.regions[r]? = some (b, sz)) (ho : o + 8 ≤ sz)
    (hw : ∀ i < 8, findWrite r (o + i) S.mem = some (.lit 0, i)) :
    WordAt m.dmem (b + BitVec.ofNat 64 o) 0 := by
  have h := hm.bytesAt_write (r := r) (o := o) (n := 8) (b := b) (sz := sz) hb ho hw
  rw [byteOf_range] at h
  exact h

end

end NativeRustcVmArm.Wire.RdRows
