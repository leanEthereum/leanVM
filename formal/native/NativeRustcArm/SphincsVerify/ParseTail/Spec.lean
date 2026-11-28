module

public import NativeRustcArm.SphincsVerify.ParseTail.Assemble

/-!
# Region 1b, the parse's tail: `ParseTailSpec`

The bytes at `8244` after `b44` are the parsed signature in rustc's layout (`sigMem_eq`): the
FORS openings, the paths (each layer's a slice of the raw signature, `flatten_slices`), the
randomizer, then per layer its chain values and its counter, the big-endian word `ldr w` loaded
and `rev` reversed (`le32_be32Of`). From `AtParse16` at `b16` the four segments (`layer0`,
`layer1`, `layer2`, `assemble`) reach `AtHMsg` at `b45`: **`parseTail_spec`**.
-/

namespace NativeRustcArm.SphincsVerifyProof.ParseTail

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym LeanVM.Protocol.KeccakHash

public section

/-- `u32::from_be_bytes` stored little-endian: the bytes reversed. -/
theorem le32_be32Of4 (a b c d : UInt8) : le32 (be32Of [a, b, c, d]) = [d, c, b, a] := by
  have ha := a.toNat_lt; have hb := b.toNat_lt; have hc := c.toNat_lt; have hd := d.toNat_lt
  simp only [le32, be32Of, beNat, leNat, be32, List.take, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.foldr, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
    simp only [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, UInt32.toNat_ofNat',
      Nat.shiftRight_eq_div_pow, UInt32.reduceToNat, Nat.reduceMod, Nat.reducePow] <;> omega

/-- A word `ldr w` loads, `rev`, stored: the bytes reversed. -/
theorem be32_load4 (a b c d : UInt8) :
    be32 (UInt32.ofNat (BitVec.ofInt 64 (Int.ofBytes [a, b, c, d])).toNat) = [d, c, b, a] := by
  have ha := a.toNat_lt; have hb := b.toNat_lt; have hc := c.toNat_lt; have hd := d.toNat_lt
  simp only [be32, Int.ofBytes, List.foldr, BitVec.toNat_ofInt, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
    simp only [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, UInt32.toNat_ofNat',
      Nat.shiftRight_eq_div_pow, UInt32.reduceToNat, Nat.reduceMod, Nat.reducePow] <;> omega

/-- **A counter's bytes**: `u32::from_be_bytes` stored little-endian are the word `ldr w` loads,
`rev` reversed, stored. -/
theorem le32_be32Of {bs : List UInt8} (h : bs.length = 4) :
    le32 (be32Of bs) = be32 (UInt32.ofNat (BitVec.ofInt 64 (Int.ofBytes bs)).toNat) := by
  match bs, h with
  | [a, b, c, d], _ => rw [le32_be32Of4, be32_load4]

variable (r : Run)

theorem le32_counter {l : Nat} (hl : l < 3) : le32 (r.layerSig l).counter = ctrBytes r l := by
  rw [r.layerSig_eq hl]
  exact le32_be32Of (length_slice (by have := sigLayerOff_le hl; rw [length_sigBytes]; omega))

theorem wots_flatten {l : Nat} (hl : l < 3) : (r.layerSig l).wots.flatten = wotsRaw r l := by
  rw [r.layerSig_eq hl]
  exact flatten_slices _ _ 64

/-- **The parsed signature's bytes** as the tail assembles them. -/
theorem sigMem_eq : sigMem r.sig = forsMem r ++ (pathsRaw r ++ (r.sig.randomizer ++
    (wotsRaw r 0 ++ (ctrBytes r 0 ++ (wotsRaw r 1 ++ (ctrBytes r 1 ++
      (wotsRaw r 2 ++ ctrBytes r 2))))))) := by
  have hp : r.sig.paths.flatten = pathsRaw r := by
    rw [Run.sig_paths, show List.range 3 = [0, 1, 2] from rfl]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatten_append,
      flatten_slices, pathsRaw, pathRaw, List.append_assoc]
  have hl : (r.sig.layers.map layerMem).flatten = wotsRaw r 0 ++ (ctrBytes r 0 ++
      (wotsRaw r 1 ++ (ctrBytes r 1 ++ (wotsRaw r 2 ++ ctrBytes r 2)))) := by
    have e : r.sig.layers = [r.layerSig 0, r.layerSig 1, r.layerSig 2] := by
      apply List.ext_getElem (by rw [r.length_layers]; rfl)
      intro i h1 _
      rw [r.layers_getElem h1]
      rw [r.length_layers] at h1
      interval_cases i <;> rfl
    rw [e]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      layerMem, List.append_assoc, wots_flatten r (show 0 < 3 by decide),
      wots_flatten r (show 1 < 3 by decide), wots_flatten r (show 2 < 3 by decide),
      le32_counter r (show 0 < 3 by decide), le32_counter r (show 1 < 3 by decide),
      le32_counter r (show 2 < 3 by decide)]
  rw [sigMem, hp, hl]
  rfl

theorem length_wotsRaw {l : Nat} (hl : l < 3) : (wotsRaw r l).length = 1024 := by
  rw [← wots_flatten r hl, length_flatten_uniform _ (r.length_wots_mem hl), r.length_wots hl]

/-- **`AtHMsg` from the facts at `b45`.** -/
theorem atHMsg_of {m : MachineData} (h : Facts r m (L45 r) (K41 r)) : r.AtHMsg m := by
  have hF := h.get (o := 8244) (n := 4224) (bs := forsMem r) (by simp [L45, L44, L41])
  have hP := h.get (o := 12468) (n := 416) (bs := pathsRaw r) (by simp [L45])
  have hR := h.get (o := 12884) (n := 16) (bs := r.sig.randomizer) (by simp [L45, L44, L41])
  have hW0 := h.get (o := 12900) (n := 1024) (bs := wotsRaw r 0) (by simp [L45, L44])
  have hc0 := h.get (o := 13924) (n := 4) (bs := ctrBytes r 0) (by simp [L45, L44])
  have hW1 := h.get (o := 13928) (n := 1024) (bs := wotsRaw r 1) (by simp [L45, L44])
  have hc1 := h.get (o := 14952) (n := 4) (bs := ctrBytes r 1) (by simp [L45, L44])
  have hW2 := h.get (o := 14956) (n := 1024) (bs := wotsRaw r 2) (by simp [L45, L44])
  have hc2 := h.get (o := 15980) (n := 4) (bs := ctrBytes r 2) (by simp [L45])
  have hcl : ∀ l, (ctrBytes r l).length = 4 := fun _ ↦ by simp [ctrBytes, be32]
  have hPl : (pathsRaw r).length = 416 := by
    simp only [pathsRaw, List.length_append, length_pathRaw r (show 0 < 3 by decide),
      length_pathRaw r (show 1 < 3 by decide), length_pathRaw r (show 2 < 3 by decide)]
    decide
  have hsig : BytesAt m.dmem (r.off 8244) (sigMem r.sig) := by
    rw [sigMem_eq r]
    exact bytesAt_cat r hF r.length_forsMem (bytesAt_cat r hP hPl (bytesAt_cat r hR
      r.length_randomizer (bytesAt_cat r hW0 (length_wotsRaw r (by decide)) (bytesAt_cat r hc0
      (hcl 0) (bytesAt_cat r hW1 (length_wotsRaw r (by decide)) (bytesAt_cat r hc1 (hcl 1)
      (bytesAt_cat r hW2 (length_wotsRaw r (by decide)) hc2)))))))
  exact ⟨h.1, ⟨h.get (o := 8208) (n := 32) (bs := pkBytes r.w)
      (by simp [L45, L44, L41, L40, L33, L25, baseL]), hsig,
      h.get (o := 376) (n := 8) (bs := wordBytes (r.addr 12468)) (by simp [L45])⟩,
    h.reg (x := .X19) (v := r.off 8208) (by simp [K41]),
    h.reg (x := .X23) (v := r.off 8244) (by simp [K41]),
    h.reg (x := .X24) (v := BitVec.ofNat 64 4640) (by simp [K41]),
    h.reg (x := .X21) (v := r.off 24720) (by simp [K41]),
    h.get (o := 432) (n := 32) (bs := r.msg) (by simp [L45, L44, L41, L40, L33, L25, baseL]),
    h.get (o := 392) (n := 8) (bs := wordBytes (r.addr 12900)) (by simp [L45, L44])⟩

variable [NativeRustcArm.Host]

/-- **Region 1b, the parse's tail**: from `AtParse16` at `b16` to `AtHMsg` at `b45`. -/
theorem parseTail_spec : ParseTailSpec := fun r hp hc hpre m h ↦
  Eventually.mono ((((layer0 r hp hc hpre).trans (layer1 r hp hc hpre)).trans
    (layer2 r hp hc hpre)).trans (assemble r hp hc hpre) m h)
    fun _ ⟨hpc, h'⟩ ↦ ⟨hpc, atHMsg_of r h'⟩

end

end NativeRustcArm.SphincsVerifyProof.ParseTail
