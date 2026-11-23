module

public import NativeRustcX64.SphincsVerify.Fors.NodeWords

/-!
# A FORS node's head (x86-64)

At a node's head (`AtNode`, `b65` at directive 730): tree `c`, height `z < 10`, the value after
`z` steps at `10368`. `b65` copies the value to `8320`, loads the two children through `cmov`ed
addresses (the copy or the path's node `z`, the carry of bit `z` of the leaf index saying which is
left), writes them to `3072` and the node's address to `9344`, spills `z + 1` (`64`) and zeroes
hasher A (`memset`): `N1` at `b66` (**`node_head`**). `b65` runs in the frame with a window
(`Run.envW`): region 0 the frame's first 20540 bytes, region 2 the path's node.
-/

namespace NativeRustcX64.SphincsVerifyProof.Fors

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym LeanVM.Protocol.KeccakHash
open NativeRustcX64.Sphincs.SphincsVerify

@[expose] public section

/-- **At `b66`**: hasher A zero, the children at `3072`, the node's address at `9344`, `z + 1` at
`64`, `c` at `104`. -/
structure N1 [Labels] (r : Run) (c z : Nat) (m : MachineData) : Prop where
  keep : Keep r c m
  hz : z < 10
  w64 : r.WordAt m 64 (z + 1).toUInt64
  w104 : r.WordAt m 104 c.toUInt64
  r12 : Run.RegIs m .r12 (r.off 4096)
  a0 : BytesAt m.dmem (r.off 4096) (List.replicate 344 0)
  ch : BytesAt m.dmem (r.off 3072) (r.childrenOf c z)
  ad : BytesAt m.dmem (r.off 9344) (r.nodeAdrsOf c z)
  r14 : Run.RegIs m .r14 (Labels.label "memcpy").toBitVec

end

public section

variable [Host] {r : Run}

omit [Host] in
/-- **A frame word loaded**, in the frame with a window. -/
theorem load_wordW [Labels] {m : MachineData} {n0 o2 : Nat} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {o : Nat} {w : UInt64} (h : BytesAt m.dmem (r.off o) (wordBytes w)) :
    (r.envW n0 o2 m vars ret).load 0 o 8 = w.toBitVec := by
  rw [Env.load_of_bytesAt (NativeRustc.length_wordBytes _) h, ofInt_ofBytes_wordBytes]

omit [Host] in
/-- **A word written** in the frame with a window. -/
theorem wordW [Labels] {m m' : MachineData} {n0 o2 : Nat} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hm : Match (r.envW n0 o2 m vars ret) S m') {o : Nat}
    (ho : o + 8 ≤ n0) {v : Sym} (hw : Chains.covers S.mem 0 o 8 v = true) {w : UInt64}
    (hv : v.eval (r.envW n0 o2 m vars ret) = w.toBitVec) : r.WordAt m' o w := by
  have := Chains.bytesAt_write_val hm (b := r.base) (sz := n0) rfl ho hw
  rwa [hv, ← Hasher.wordBytes_ofBitVec] at this

omit [Host] in
theorem ite_eval_true [Labels] {env : Env} {b : SBool} {x y : Sym} (h : b.eval env = true) :
    (Sym.ite b x y).eval env = x.eval env := by
  simp [Sym.eval, h]

omit [Host] in
theorem ite_eval_false [Labels] {env : Env} {b : SBool} {x y : Sym} (h : b.eval env = false) :
    (Sym.ite b x y).eval env = y.eval env := by
  simp [Sym.eval, h]

omit [Host] in
theorem shl4 (z : Nat) :
    BinOp.apply .shl .W64 (BitVec.ofNat 64 z) (BitVec.ofNat 64 4) = BitVec.ofNat 64 (16 * z) := by
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [shiftCount_lit .W64 4 (by simp [Width.bits])]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Width.bits]
  omega

/-- **A node's head**: from `AtNode r c z` at `b65`, `N1 r c z` at `b66`. -/
theorem node_head (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {c z : Nat} {m : MachineData} (h : AtNode r c z m) {R : MachineState → Prop}
    (cont : ∀ m', N1 r c z m' → Eventually (step1 Host.exe) R ⟨m', r.pc NativeRustcX64.Sphincs.SphincsVerify.b66Offset⟩) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b65Offset⟩ := by
  obtain ⟨hK, hz, hcx, h13, h12, h15, hbp, w104, hcur, hbx, h14⟩ := h
  have hc24 := hK.2.1.hc
  have hleaf := r.leafOf_lt hc24
  have hcx' : m.regs.get64 .rcx = BitVec.ofNat 64 z := hcx
  have h13' : m.regs.get64 .r13 = BitVec.ofNat 64 c := h13
  have hwf := r.wfW hpre hK.1.2.2.2 (n0 := 20540) (o2 := 20540 + 176 * c + 16 * z) (by omega)
    (by omega) (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b66Offset).toBitVec
  have h72 := load_wordW (n0 := 20540) (o2 := 20540 + 176 * c + 16 * z) (vars := fun _ ↦ 0)
    (ret := (r.pc NativeRustcX64.Sphincs.SphincsVerify.b66Offset).toBitVec) hK.2.2.1
  have h88 := load_wordW (n0 := 20540) (o2 := 20540 + 176 * c + 16 * z) (vars := fun _ ↦ 0)
    (ret := (r.pc NativeRustcX64.Sphincs.SphincsVerify.b66Offset).toBitVec) hK.2.2.2
  have hm : Match (r.envW 20540 (20540 + 176 * c + 16 * z) m (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b66Offset).toBitVec)
      s65 m := by
    refine r.matchW hK.1 (known := [(.rbx, .label "memset")]) (bounds := [(.reg .rcx, 10)])
      (aliases := [(pathSym, 2, 0)]) ⟨hbx, trivial⟩
      ⟨by show (m.regs.get64 .rcx).toNat < 10; rw [hcx']; simp; omega, trivial⟩ ⟨?_, trivial⟩
    show (Sym.load 0 72 8).eval _ + BinOp.apply .shl .W64 (m.regs.get64 .rcx)
      (BitVec.ofNat 64 4) = r.off (20540 + 176 * c + 16 * z) + BitVec.ofInt 64 0
    rw [show (Sym.load 0 72 8).eval (r.envW 20540 (20540 + 176 * c + 16 * z) m (fun _ ↦ 0)
      (r.pc NativeRustcX64.Sphincs.SphincsVerify.b66Offset).toBitVec) = _ from h72, hcx', shl4 z,
      show BitVec.ofInt 64 0 = 0#64 by decide, BitVec.add_zero]
    exact Run.off_add r _ _
  refine Chains.blk r hp b65_in_code (List.cons_ne_nil _ _) run_b65 hwf (fun _ _ ↦ rfl) hm
    fun st₁ hm₁ hpc₁ ↦ ?_
  have keptW : KeptBy r _ m st₁.data := fun ho hn h ↦ r.bytesAt_keptW' hpre hm₁ hwf ho h hn
  have hK₁ : KeepC r c st₁.data :=
    ⟨Run.AtCall.of_matchW r hpre hK.1 (by decide) (by omega) hm₁ hwf rfl (by decide +kernel),
      hK.2.1.of_kept keptW (by decide +kernel), hK.2.2.of_kept keptW (by decide +kernel)⟩
  have hb0 : (r.envW 20540 (20540 + 176 * c + 16 * z) m (fun _ ↦ 0)
      (r.pc NativeRustcX64.Sphincs.SphincsVerify.b66Offset).toBitVec).regions[0]? = some (r.base, 20540) := rfl
  -- `z + 1` at `64`
  have w64 : r.WordAt st₁.data 64 (z + 1).toUInt64 :=
    wordW hm₁ (o := 64) (v := .bin .add .W64 (.reg .rcx) (.lit 1)) (by decide) (by decide +kernel)
      (by
        show BinOp.apply .add .W64 (m.regs.get64 .rcx) (BitVec.ofNat 64 1) = _
        rw [hcx']
        simp [BinOp.apply]
        rfl)
  -- the children
  have hC := bit_eval (env := r.envW 20540 (20540 + 176 * c + 16 * z) m (fun _ ↦ 0)
    (r.pc NativeRustcX64.Sphincs.SphincsVerify.b66Offset).toBitVec) (l := r.leafOf c) hz h88 hcx'
  have hcurE : BytesAt (r.envW 20540 (20540 + 176 * c + 16 * z) m (fun _ ↦ 0)
      (r.pc NativeRustcX64.Sphincs.SphincsVerify.b66Offset).toBitVec).mem0 (r.base + BitVec.ofNat 64 10368) (r.forsUpTo c z) := hcur
  have hpathE : BytesAt (r.envW 20540 (20540 + 176 * c + 16 * z) m (fun _ ↦ 0)
      (r.pc NativeRustcX64.Sphincs.SphincsVerify.b66Offset).toBitVec).mem0 (r.off (20540 + 176 * c + 16 * z) + BitVec.ofNat 64 0)
      (r.pathNode c z) := Chains.bytesAt_add_zero (hK.2.1.pathNode hz)
  have hcl := r.length_forsUpTo c z
  have hpl := r.length_pathNode hc24 hz
  have ch : BytesAt st₁.data.dmem (r.off 3072) (r.childrenOf c z) := by
    unfold Run.childrenOf
    split
    · rename_i hbit
      simp only [hbit, decide_true, Bool.not_true] at hC
      have hnC : (SBool.not bitC).eval (r.envW 20540 (20540 + 176 * c + 16 * z) m (fun _ ↦ 0)
          (r.pc NativeRustcX64.Sphincs.SphincsVerify.b66Offset).toBitVec) = true := by
        show (!_) = true
        rw [hC]
        rfl
      exact Chains.BytesAt.cat
        (write16 hm₁ hb0 (o := 3072) (by decide)
          (v₁ := .ite (.not bitC) (.load 0 10368 8) (.load 2 0 8))
          (v₂ := .ite (.not bitC) (.load 0 10376 8) (.load 2 8 8)) (by decide +kernel)
          (by decide +kernel) (ite_eval_true hnC) (ite_eval_true hnC) hcl hcurE)
        (write16 hm₁ hb0 (o := 3088) (by decide)
          (v₁ := .ite bitC (.load 0 10368 8) (.load 2 0 8))
          (v₂ := .ite bitC (.load 0 10376 8) (.load 2 8 8)) (by decide +kernel)
          (by decide +kernel) (ite_eval_false hC) (ite_eval_false hC) hpl hpathE) (by rw [hcl])
    · rename_i hbit
      simp only [hbit, decide_false, Bool.not_false] at hC
      have hnC : (SBool.not bitC).eval (r.envW 20540 (20540 + 176 * c + 16 * z) m (fun _ ↦ 0)
          (r.pc NativeRustcX64.Sphincs.SphincsVerify.b66Offset).toBitVec) = false := by
        show (!_) = false
        rw [hC]
        rfl
      exact Chains.BytesAt.cat
        (write16 hm₁ hb0 (o := 3072) (by decide)
          (v₁ := .ite (.not bitC) (.load 0 10368 8) (.load 2 0 8))
          (v₂ := .ite (.not bitC) (.load 0 10376 8) (.load 2 8 8)) (by decide +kernel)
          (by decide +kernel) (ite_eval_false hnC) (ite_eval_false hnC) hpl hpathE)
        (write16 hm₁ hb0 (o := 3088) (by decide)
          (v₁ := .ite bitC (.load 0 10368 8) (.load 2 0 8))
          (v₂ := .ite bitC (.load 0 10376 8) (.load 2 8 8)) (by decide +kernel)
          (by decide +kernel) (ite_eval_true hC) (ite_eval_true hC) hcl hcurE) (by rw [hpl])
  -- the node's address
  have ad : BytesAt st₁.data.dmem (r.off 9344) (r.nodeAdrsOf c z) := by
    rw [nodeAdrs_eq]
    have a0 := Chains.bytesAt_write_val hm₁ hb0 (o := 9344) (n := 8) (v := .lit 0) (by decide)
      (by decide +kernel)
    rw [show Sym.eval _ (.lit 0) = BitVec.ofNat 64 0 from rfl, bytes_zero8] at a0
    have a1 := Chains.bytesAt_write_val hm₁ hb0 (o := 9352) (n := 8) (v := .reg .r15) (by decide)
      (by decide +kernel)
    rw [show Sym.eval _ (.reg .r15) = reg m .r15 from rfl, bytes_word, h15] at a1
    have a2 := Chains.bytesAt_write_val hm₁ hb0 (o := 9360) (n := 4) (v := .lit 50331648)
      (by decide) (by decide +kernel)
    rw [show Sym.eval _ (.lit 50331648) = BitVec.ofNat 64 50331648 from rfl, bytes_typeW] at a2
    have a3 := Chains.bytesAt_write_val hm₁ hb0 (o := 9364) (n := 4)
      (v := .un .trunc .W32 (.reg .rbp))
      (by decide) (by decide +kernel)
    rw [show Sym.eval _ (.un .trunc .W32 (.reg .rbp)) = UnOp.apply .trunc .W32 (reg m .rbp) from
      rfl,
      Digest.bytes_trunc32, hbp, List.take_left' (show (be32 (r.key 0).leaf).length = 4 from rfl)]
      at a3
    have a4 := Chains.bytesAt_write_val hm₁ hb0 (o := 9368) (n := 4)
      (v := .un .trunc .W32 (.un .bswap .W32 (.un .trunc .W32
        (.bin .add .W64 (.reg .rcx) (.lit 1)))))
      (by decide) (by decide +kernel)
    rw [show Sym.eval (r.envW 20540 (20540 + 176 * c + 16 * z) m (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b66Offset).toBitVec)
      (.un .trunc .W32 (.un .bswap .W32 (.un .trunc .W32 (.bin .add .W64 (.reg .rcx) (.lit 1))))) =
      UnOp.apply .trunc .W32 (UnOp.apply .bswap .W32 (UnOp.apply .trunc .W32
        (BinOp.apply .add .W64 (m.regs.get64 .rcx) (BitVec.ofNat 64 1)))) from rfl, hcx',
      bytes_height] at a4
    have a5 := Chains.bytesAt_write_val hm₁ hb0 (o := 9372) (n := 4)
      (v := .un .trunc .W32 (.un .bswap .W32 (.bin .add .W32
        (.bin .shl .W32 (.un .trunc .W32 (.reg .r13))
        (.bin .merge .W8 (.bin .merge .W8 (.bin .add .W64 (.reg .rcx) (.lit 1)) (.lit 9))
          (.bin .sub .W8 (.bin .merge .W8 (.bin .add .W64 (.reg .rcx) (.lit 1)) (.lit 9))
            (.un .trunc .W32 (.reg .rcx)))))
        (.bin .shr .W64 (.load 0 88 8) (.bin .add .W64 (.reg .rcx) (.lit 1))))))
      (by decide) (by decide +kernel)
    rw [show Sym.eval (r.envW 20540 (20540 + 176 * c + 16 * z) m (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b66Offset).toBitVec)
      (.un .trunc .W32 (.un .bswap .W32 (.bin .add .W32
        (.bin .shl .W32 (.un .trunc .W32 (.reg .r13))
        (.bin .merge .W8 (.bin .merge .W8 (.bin .add .W64 (.reg .rcx) (.lit 1)) (.lit 9))
          (.bin .sub .W8 (.bin .merge .W8 (.bin .add .W64 (.reg .rcx) (.lit 1)) (.lit 9))
            (.un .trunc .W32 (.reg .rcx)))))
        (.bin .shr .W64 (.load 0 88 8) (.bin .add .W64 (.reg .rcx) (.lit 1)))))) =
      UnOp.apply .trunc .W32 (UnOp.apply .bswap .W32 (BinOp.apply .add .W32
        (BinOp.apply .shl .W32 (UnOp.apply .trunc .W32 (BitVec.ofNat 64 c)) (clW z))
        (BinOp.apply .shr .W64 (BitVec.ofNat 64 (r.leafOf c))
          (BinOp.apply .add .W64 (BitVec.ofNat 64 z) (BitVec.ofNat 64 1))))) by
      show UnOp.apply .trunc .W32 (UnOp.apply .bswap .W32 (BinOp.apply .add .W32
        (BinOp.apply .shl .W32 (UnOp.apply .trunc .W32 (m.regs.get64 .r13))
          (BinOp.apply .merge .W8 (BinOp.apply .merge .W8
            (BinOp.apply .add .W64 (m.regs.get64 .rcx) (BitVec.ofNat 64 1)) (BitVec.ofNat 64 9))
            (BinOp.apply .sub .W8 (BinOp.apply .merge .W8
              (BinOp.apply .add .W64 (m.regs.get64 .rcx) (BitVec.ofNat 64 1)) (BitVec.ofNat 64 9))
              (UnOp.apply .trunc .W32 (m.regs.get64 .rcx)))))
        (BinOp.apply .shr .W64 ((r.envW 20540 (20540 + 176 * c + 16 * z) m (fun _ ↦ 0)
          (r.pc NativeRustcX64.Sphincs.SphincsVerify.b66Offset).toBitVec).load 0 88 8)
          (BinOp.apply .add .W64 (m.regs.get64 .rcx) (BitVec.ofNat 64 1))))) = _
      rw [h13', h88, hcx']
      rfl, bytes_nodeIndex hc24 hz hleaf] at a5
    exact Digest.bytesAt_cat a0 rfl rfl (Digest.bytesAt_cat a1 rfl rfl (Digest.bytesAt_cat a2 rfl
      rfl (Digest.bytesAt_cat a3 rfl rfl (Digest.bytesAt_cat a4 rfl rfl a5))))
  -- `memset` of hasher A
  have hadl := length_forsNodeAdrs r.idx c (z + 1) (r.leafOf c >>> (z + 1))
  have hchl := r.length_childrenOf hc24 hz
  refine memset_then hpre hc hpc₁ hK₁ (a := 4096) (n := 344) ((hm₁.regs .rdi _ rfl).trans h12)
    (Chains.toNat_of_lit hm₁ rfl (by decide)) (Chains.toNat_of_lit hm₁ rfl (by decide))
    (by decide) fun m₂ hK₂ hS₂ hkc₂ hz₂ ↦ cont m₂ ⟨hK₂, hz, hkc₂ (by flen) (by flen) w64,
      hkc₂ (by flen) (by flen) (keptW (by flen)
        (by rw [NativeRustc.length_wordBytes]; decide +kernel) w104), Chains.RegIs.of_saved hS₂ rfl (Chains.regIs_reg hm₁ rfl h12), hz₂,
      hkc₂ (by rw [hchl]; omega) (by rw [hchl]; omega) ch,
      hkc₂ (by rw [Run.nodeAdrsOf, hadl]; omega) (by rw [Run.nodeAdrsOf, hadl]; omega) ad,
      Chains.RegIs.of_saved hS₂ rfl (Chains.regIs_reg hm₁ rfl h14)⟩

end

end NativeRustcX64.SphincsVerifyProof.Fors
