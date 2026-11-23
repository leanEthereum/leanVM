module

public import NativeRustcX64.SphincsVerify.Fors.State

/-!
# A FORS tree's head and leaf (x86-64)

From tree `c`'s head (`AtTree`, `b58`): `b58` spills the opening's address
(`104`), the secret's (`8`), the leaf index (`72`) and `c` (`88`), writes the leaf's address
at `2056` and zeroes hasher A (`memset`); `b59`, `b60` absorb `PK.seed` and the address,
`b61` clones A into hasher B (`memcpy`), `b62` absorbs the secret into B, and `b63` finalizes
B to `8328`; `b64` starts the nodes at height 0 (`AtNode r c 0` at `b65`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Fors

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym LeanVM.Protocol.KeccakHash
open NativeRustcX64.Sphincs.SphincsVerify
open NativeRustcX64.SphincsVerifyProof.Digest (HasherAt)

public section

variable [Host] {r : Run}

omit [Host] in
theorem eval_ptr0 [Labels] {m : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64} :
    (Sym.ptr 0 0).eval (r.env m vars ret) = r.base := by
  simp [Sym.eval]

omit [Host] in
/-- The opening's (and the secret's) address, as `b58` computes it. -/
theorem eval_openAddr [Labels] {m : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64}
    (hpre : r.Pre) {c : Nat} (hc : c < 24) (h13 : m.regs.get64 .rsi = BitVec.ofNat 64 c)
    {o : Nat} (ho : o ≤ 20716) :
    (Sym.bin .add .W64 (.lit o) (.bin .add .W64 (.ptr 0 0)
      (.bin .mul .W64 (.reg .rsi) (.lit 176)))).eval (r.env m vars ret) =
      (r.addr (o + 176 * c)).toBitVec := by
  have hb := r.base_toNat hpre
  have ho' := r.off_toNat hpre (a := o + 176 * c) (by omega)
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, h13, Run.env_base0]
  rw [show BitVec.ofInt 64 0 = 0#64 by decide, BitVec.add_zero]
  show BitVec.ofNat 64 o + (r.base + BitVec.ofNat 64 c * BitVec.ofNat 64 176) = r.off (o + 176 * c)
  apply BitVec.eq_of_toNat_eq
  rw [ho']
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

omit [Host] in
theorem mul8 (c : Nat) (hc : c < 24) :
    (BinOp.apply .mul .W64 (BitVec.ofNat 64 c) (BitVec.ofNat 64 8)).toNat = 8 * c := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

omit [Host] in
/-- The bytes of a register's low 4 bytes stored. -/
theorem bytesAt_trunc4' [Labels] {m m₁ : MachineData} {ret : BitVec 64} {S : SState}
    (hm : Match (r.env m (fun _ ↦ 0) ret) S m₁) {o : Nat} {y : Reg64} (ho : o + 4 ≤ 29408)
    (hw : ∀ i < 4, findWrite 0 (o + i) S.mem = some (.un .trunc .W32 (.reg y), i)) {k : List UInt8}
    (hy : wordBytes (UInt64.ofBitVec (reg m y)) = k ++ [0, 0, 0, 0]) (hk : k.length = 4) :
    BytesAt m₁.dmem (r.off o) k := by
  have := Digest.bytesAt_trunc4 hm (o := o) (y := y) ho hw
  rwa [hy, List.take_left' hk] at this

/-- **A tree's head and leaf**: from `AtTree r c` at `b58`, `AtNode r c 0` at `b65`. -/
theorem tree_head (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {c : Nat} {m : MachineData} (h : AtTree r c m) {R : MachineState → Prop}
    (cont : ∀ m', AtNode r c 0 m' → Eventually (step1 Host.exe) R ⟨m', r.pc NativeRustcX64.Sphincs.SphincsVerify.b65Offset⟩) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b58Offset⟩ := by
  obtain ⟨hK, h13, h12, h14, h15, hbp, hbx, hBptr⟩ := h
  have hc24 := hK.2.c_lt
  have hleaf := r.leafOf_lt hc24
  have h13' : m.regs.get64 .rsi = BitVec.ofNat 64 c := h13
  -- b58: the spills, the leaf's address, `memset` of hasher A
  have hwf := r.frame_wf hpre hK.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b59Offset).toBitVec
  have hm : Match (r.env m (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b59Offset).toBitVec) s58 m :=
    r.match_frame hpre hK.1 (known := [(.rbx, .label "memset")]) (labels := [])
      (bounds := [(.reg .rsi, 24)]) (aliases := []) ⟨hbx, trivial⟩ trivial
      ⟨by show (m.regs.get64 .rsi).toNat < 24; rw [h13']; simp; omega, trivial⟩
      trivial
  refine Chains.blk r hp b58_in_code (List.cons_ne_nil _ _) run_b58 hwf (fun _ _ ↦ rfl) hm
    fun st₁ hm₁ hpc₁ ↦ ?_
  have hK₁ := KeepC0.of_block hpre hK hm₁ hwf (by decide +kernel) rfl
  have hload : (r.env m (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b59Offset).toBitVec).load 0
      (10384 + (BinOp.apply .mul .W64 (m.regs.get64 .rsi) (BitVec.ofNat 64 8)).toNat) 8 =
      (r.leafOf c).toUInt64.toBitVec := by
    rw [h13', mul8 c hc24]
    exact Chains.load_word (wordAt_leaf hK.2.leaves hc24)
  have w72 : r.WordAt st₁.data 104 (r.addr (20556 + 176 * c)) :=
    Chains.frame_write_word hm₁ (o := 104) (by decide) (by decide +kernel)
      (eval_openAddr hpre hc24 h13' (by omega))
  have w8 : r.WordAt st₁.data 8 (r.addr (20716 + 176 * c)) :=
    Chains.frame_write_word hm₁ (o := 8)
      (v := .bin .add .W64 (.bin .add .W64 (.ptr 0 0)
        (.bin .mul .W64 (.reg .rsi) (.lit 176))) (.lit 20716))
      (by decide) (by decide +kernel)
      (by simpa only [Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.add_comm] using
        (eval_openAddr hpre hc24 h13' (o := 20716) (by omega)))
  have w88 : r.WordAt st₁.data 72 (r.leafOf c).toUInt64 :=
    Chains.frame_write_word hm₁ (o := 72)
      (v := .loadx 0 10384 (.bin .mul .W64 (.reg .rsi) (.lit 8)) 8)
      (by decide) (by decide +kernel) hload
  have wCount : r.WordAt st₁.data 88 c.toUInt64 :=
    Chains.frame_write_word hm₁ (o := 88) (v := .reg .rsi) (by decide) (by decide +kernel) h13
  have had : BytesAt st₁.data.dmem (r.off 2056) (forsNodeAdrs r.idx c 0 (r.leafOf c)) := by
    rw [leafAdrs_eq]
    have a0 := Digest.bytesAt_lit8 hm₁ (o := 2056) (v := 0) (by decide) (by decide +kernel)
      bytes_zero8
    have a1 := Digest.bytesAt_reg8 hm₁ (o := 2064) (y := .r13) (by decide) (by decide +kernel)
    rw [h15] at a1
    have a2 := Digest.bytesAt_lit4 hm₁ (o := 2072) (v := 50331648) (by decide)
      (by decide +kernel) bytes_typeW
    have a3 := bytesAt_trunc4' hm₁ (o := 2076) (y := .rbp) (by decide) (by decide +kernel) hbp rfl
    have a4 := Digest.bytesAt_lit4 hm₁ (o := 2080) (v := 0) (by decide) (by decide +kernel)
      bytes_zero4
    have a5 := Chains.frame_write_val hm₁ (o := 2084) (n := 4)
      (v := .un .trunc .W32 (.un .bswap .W32 (.bin .add .W32
        (.loadx 0 10384 (.bin .mul .W64 (.reg .rsi) (.lit 8)) 8)
        (.bin .shl .W32 (.un .trunc .W32 (.reg .rsi)) (.lit 10))))) (by decide) (by decide +kernel)
    have hv : Sym.eval (r.env m (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b59Offset).toBitVec) (.un .trunc .W32 (.un .bswap .W32
        (.bin .add .W32 (.loadx 0 10384 (.bin .mul .W64 (.reg .rsi) (.lit 8)) 8)
        (.bin .shl .W32 (.un .trunc .W32 (.reg .rsi)) (.lit 10))))) =
        UnOp.apply .trunc .W32 (UnOp.apply .bswap .W32 (BinOp.apply .add .W32
          (BitVec.ofNat 64 (r.leafOf c)) (BinOp.apply .shl .W32
            (UnOp.apply .trunc .W32 (BitVec.ofNat 64 c)) (BitVec.ofNat 64 10)))) := by
      show UnOp.apply .trunc .W32 (UnOp.apply .bswap .W32 (BinOp.apply .add .W32
        ((r.env m (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b59Offset).toBitVec).load 0
          (10384 + (BinOp.apply .mul .W64 (m.regs.get64 .rsi) (BitVec.ofNat 64 8)).toNat) 8)
        (BinOp.apply .shl .W32 (UnOp.apply .trunc .W32 (m.regs.get64 .rsi))
          (BitVec.ofNat 64 10)))) = _
      rw [hload, h13']
      rfl
    rw [hv, bytes_leafIndex hc24] at a5
    exact Digest.bytesAt_cat a0 rfl rfl (Digest.bytesAt_cat a1 rfl rfl (Digest.bytesAt_cat a2 rfl
      rfl (Digest.bytesAt_cat a3 rfl rfl (Digest.bytesAt_cat a4 rfl rfl a5))))
  have hadl := length_forsNodeAdrs r.idx c 0 (r.leafOf c)
  have hseedl := Digest.length_seed r
  have hsecl := r.length_secret hc24
  -- `memset` of hasher A
  have h0 : Run.RegIs st₁.data .rdi (r.off 4104) := (hm₁.regs .rdi _ rfl).trans h12
  refine memset_then hpre hc hpc₁ ⟨hK₁.1, hK₁.2, w72, w88⟩ (a := 4104) (n := 344) h0
    (Chains.toNat_of_lit hm₁ rfl (by decide)) (Chains.toNat_of_lit hm₁ rfl (by decide))
    (by decide) fun m₂ hK₂ hS₂ hkc₂ hz₂ ↦ ?_
  have g13 := hkc₂ (by flen) (by flen) wCount
  have gBptr := Chains.RegIs.of_saved hS₂ rfl (Chains.regIs_reg hm₁ rfl hBptr)
  have g12 := Chains.RegIs.of_saved hS₂ rfl (Chains.regIs_reg hm₁ rfl h12)
  have g14 := Chains.RegIs.of_saved hS₂ rfl (Chains.regIs_reg hm₁ rfl h14)
  have g15 := Chains.RegIs.of_saved hS₂ rfl (Chains.regIs_reg (v := reg m .r13) hm₁ rfl rfl)
  have gbp := Chains.RegIs.of_saved hS₂ rfl (Chains.regIs_reg (v := reg m .rbp) hm₁ rfl rfl)
  have g8 := hkc₂ (by flen) (by flen) w8
  have gad := hkc₂ (by rw [hadl]; omega) (by rw [hadl]; omega) had
  have gH : HasherAt r m₂ 4104 [] := ⟨_, hz₂, Keccak.holds_new⟩
  -- b59: `PK.seed`
  have hwf₂ := r.frame_wf hpre hK₂.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b60Offset).toBitVec
  refine Chains.blk r hp b59_in_code (j := NativeRustcX64.Sphincs.SphincsVerify.b59Offset) (List.cons_ne_nil _ _) run_b59 hwf₂
    (fun _ _ ↦ rfl) (match_frameS hpre hK₂.1 ⟨Chains.known_ptr g12, Chains.known_ptr g14, trivial⟩)
    fun st₃ hm₃ hpc₃ ↦ ?_
  refine update_then hpre hc hpc₃ (KeepC.of_block hpre hK₂ hm₃ hwf₂ (by decide +kernel) rfl)
    (a := 4104) (b := 112) (n := 16) (Chains.regIs_ptr hm₃ rfl) (Chains.regIs_ptr hm₃ rfl)
    (Chains.toNat_of_lit hm₃ rfl (by decide))
    (by decide) (by decide) (by decide) hseedl
    (HasherAt.kept hpre gH hm₃ hwf₂ (by decide) (by decide +kernel))
    (r.bytesAt_kept hpre hm₃ hwf₂ (by flen) hK₂.seed (by rw [hseedl]; decide +kernel))
    fun m₄ hK₄ hS₄ hkc₄ hH₄ ↦ ?_
  have g13 := hkc₄ (by flen) (by flen)
    (r.bytesAt_kept hpre hm₃ hwf₂ (by flen) g13 (by rw [NativeRustc.length_wordBytes]; decide +kernel))
  have gBptr := Chains.RegIs.of_saved hS₄ rfl (Chains.regIs_reg hm₃ rfl gBptr)
  have g12 : Run.RegIs m₄ .r12 (r.off 4104) :=
    Chains.RegIs.of_saved hS₄ rfl (Chains.regIs_ptr hm₃ rfl)
  have g15 := Chains.RegIs.of_saved hS₄ rfl (Chains.regIs_reg hm₃ rfl g15)
  have gbp := Chains.RegIs.of_saved hS₄ rfl (Chains.regIs_reg hm₃ rfl gbp)
  have g8 := hkc₄ (by flen) (by flen)
    (r.bytesAt_kept hpre hm₃ hwf₂ (by flen) g8
      (by rw [NativeRustc.length_wordBytes]; decide +kernel))
  have gad := hkc₄ (by rw [hadl]; omega) (by rw [hadl]; omega)
    (r.bytesAt_kept hpre hm₃ hwf₂ (by rw [hadl]; omega) gad (by rw [hadl]; decide +kernel))
  -- b60: the leaf's address
  have hwf₄ := r.frame_wf hpre hK₄.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b61Offset).toBitVec
  refine Chains.blk r hp b60_in_code (j := NativeRustcX64.Sphincs.SphincsVerify.b60Offset) (List.cons_ne_nil _ _) run_b60 hwf₄
    (fun _ _ ↦ rfl) (match_frameS hpre hK₄.1 ⟨Chains.known_ptr g12, trivial⟩) fun st₅ hm₅ hpc₅ ↦ ?_
  refine update_then hpre hc hpc₅ (KeepC.of_block hpre hK₄ hm₅ hwf₄ (by decide +kernel) rfl)
    (a := 4104) (b := 2056) (n := 32) (Chains.regIs_ptr hm₅ rfl) (Chains.regIs_ptr hm₅ rfl)
    (Chains.toNat_of_lit hm₅ rfl (by decide))
    (by decide) (by decide) (by decide) hadl
    (HasherAt.kept hpre hH₄ hm₅ hwf₄ (by decide) (by decide +kernel))
    (r.bytesAt_kept hpre hm₅ hwf₄ (by rw [hadl]; omega) gad (by rw [hadl]; decide +kernel))
    fun m₆ hK₆ hS₆ hkc₆ hH₆ ↦ ?_
  have g13 := hkc₆ (by flen) (by flen)
    (r.bytesAt_kept hpre hm₅ hwf₄ (by flen) g13 (by rw [NativeRustc.length_wordBytes]; decide +kernel))
  have gBptr := Chains.RegIs.of_saved hS₆ rfl (Chains.regIs_reg hm₅ rfl gBptr)
  have g12 : Run.RegIs m₆ .r12 (r.off 4104) :=
    Chains.RegIs.of_saved hS₆ rfl (Chains.regIs_ptr hm₅ rfl)
  have g15 := Chains.RegIs.of_saved hS₆ rfl (Chains.regIs_reg hm₅ rfl g15)
  have gbp := Chains.RegIs.of_saved hS₆ rfl (Chains.regIs_reg hm₅ rfl gbp)
  have g8 := hkc₆ (by flen) (by flen)
    (r.bytesAt_kept hpre hm₅ hwf₄ (by flen) g8
      (by rw [NativeRustc.length_wordBytes]; decide +kernel))
  -- b61: the clone into hasher B
  have hwf₆ := r.frame_wf hpre hK₆.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b62Offset).toBitVec
  refine Chains.blk r hp b61_in_code (j := NativeRustcX64.Sphincs.SphincsVerify.b61Offset) (List.cons_ne_nil _ _) run_b61 hwf₆
    (fun _ _ ↦ rfl) (match_frameS hpre hK₆.1 ⟨Chains.known_ptr g12, Chains.known_ptr gBptr, trivial⟩) fun st₇ hm₇ hpc₇ ↦ ?_
  obtain ⟨hA, hAb, hAh⟩ := HasherAt.kept hpre hH₆ hm₇ hwf₆ (by decide) (by decide +kernel)
  refine memcpy_then hpre hc hpc₇ (KeepC.of_block hpre hK₆ hm₇ hwf₆ (by decide +kernel) rfl)
    (a := 560) (b := 4104) (n := 344) (Chains.regIs_ptr hm₇ rfl) (Chains.regIs_ptr hm₇ rfl)
    (Chains.toNat_of_lit hm₇ rfl (by decide)) (by decide) (by decide) (by decide)
    (Keccak.length_of_holds hAh) hAb fun m₈ hK₈ hS₈ hkc₈ hB₈ ↦ ?_
  have g13 := hkc₈ (by flen) (by flen)
    (r.bytesAt_kept hpre hm₇ hwf₆ (by flen) g13 (by rw [NativeRustc.length_wordBytes]; decide +kernel))
  have g12 : Run.RegIs m₈ .r12 (r.off 4104) :=
    Chains.RegIs.of_saved hS₈ rfl (Chains.regIs_ptr hm₇ rfl)
  have gBptr : Run.RegIs m₈ .r15 (r.off 560) :=
    Chains.RegIs.of_saved hS₈ rfl (Chains.regIs_ptr hm₇ rfl)
  have g15 := Chains.RegIs.of_saved hS₈ rfl (Chains.regIs_reg hm₇ rfl g15)
  have gbp := Chains.RegIs.of_saved hS₈ rfl (Chains.regIs_reg hm₇ rfl gbp)
  have g14 := Chains.RegIs.of_saved hS₈ rfl (Chains.regIs_label (y := .r14) hm₇ rfl)
  have g8 := hkc₈ (by flen) (by flen)
    (r.bytesAt_kept hpre hm₇ hwf₆ (by flen) g8
      (by rw [NativeRustc.length_wordBytes]; decide +kernel))
  have gB : HasherAt r m₈ 560 (r.seed ++ forsNodeAdrs r.idx c 0 (r.leafOf c)) := ⟨hA, hB₈, hAh⟩
  -- b62: the secret
  have hwf₈ := r.frame_wf hpre hK₈.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b63Offset).toBitVec
  refine Chains.blk r hp b62_in_code (j := NativeRustcX64.Sphincs.SphincsVerify.b62Offset) (List.cons_ne_nil _ _) run_b62 hwf₈
    (fun _ _ ↦ rfl) (match_frameS hpre hK₈.1 ⟨Chains.known_ptr gBptr, g14, trivial⟩) fun st₉ hm₉ hpc₉ ↦ ?_
  have h1 : Run.RegIs st₉.data .rsi (r.off (20716 + 176 * c)) := by
    unfold Run.RegIs reg
    rw [hm₉.regs .rsi _ rfl, Chains.load_word g8]
    rfl
  refine update_then hpre hc hpc₉ (KeepC.of_block hpre hK₈ hm₉ hwf₈ (by decide +kernel) rfl)
    (a := 560) (n := 16) (Chains.regIs_ptr hm₉ rfl) h1 (Chains.toNat_of_lit hm₉ rfl (by decide))
    (by decide)
    (by omega) (by omega) hsecl (HasherAt.kept hpre gB hm₉ hwf₈ (by decide) (by decide +kernel))
    (r.bytesAt_kept hpre hm₉ hwf₈ (by rw [hsecl]; omega) hK₈.2.1.secret (by
      rw [hsecl]
      refine Chains.noWriteIn_mono (o := 20172) (n := 8124) ?_ (by omega) (by omega)
      decide +kernel)) fun m₁₀ hK₁₀ hS₁₀ hkc₁₀ hH₁₀ ↦ ?_
  have g13 := hkc₁₀ (by flen) (by flen)
    (r.bytesAt_kept hpre hm₉ hwf₈ (by flen) g13 (by rw [NativeRustc.length_wordBytes]; decide +kernel))
  have gBptr := Chains.RegIs.of_saved hS₁₀ rfl (Chains.regIs_ptr (y := .r15) hm₉ rfl)
  have g12 := Chains.RegIs.of_saved hS₁₀ rfl (Chains.regIs_reg hm₉ rfl g12)
  have g15 := Chains.RegIs.of_saved hS₁₀ rfl (Chains.regIs_reg hm₉ rfl g15)
  have gbp := Chains.RegIs.of_saved hS₁₀ rfl (Chains.regIs_reg hm₉ rfl gbp)
  have gbx := Chains.RegIs.of_saved hS₁₀ rfl (Chains.regIs_label (y := .rbx) hm₉ rfl)
  have g14 := Chains.RegIs.of_saved hS₁₀ rfl (Chains.regIs_label (y := .r14) hm₉ rfl)
  -- b63: `finalize` into `8328`
  have hwf₁₀ := r.frame_wf hpre hK₁₀.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b64Offset).toBitVec
  refine Chains.blk r hp b63_in_code (j := NativeRustcX64.Sphincs.SphincsVerify.b63Offset) (List.cons_ne_nil _ _) run_b63 hwf₁₀
    (fun _ _ ↦ rfl) (match_frameS hpre hK₁₀.1 ⟨Chains.known_ptr gBptr, trivial⟩) fun st₁₁ hm₁₁ hpc₁₁ ↦ ?_
  refine finalize_then hpre hc hpc₁₁ (KeepC.of_block hpre hK₁₀ hm₁₁ hwf₁₀ (by decide +kernel) rfl)
    (o := 8328) (a := 560) (Chains.regIs_ptr hm₁₁ rfl) (Chains.regIs_ptr hm₁₁ rfl) (by decide)
    (by decide) (by decide) (HasherAt.kept hpre hH₁₀ hm₁₁ hwf₁₀ (by decide) (by decide +kernel))
    fun m₁₂ hK₁₂ hS₁₂ hkc₁₂ hD ↦ ?_
  have g13 := hkc₁₂ (by flen) (by flen)
    (r.bytesAt_kept hpre hm₁₁ hwf₁₀ (by flen) g13 (by rw [NativeRustc.length_wordBytes]; decide +kernel))
  have g12 := Chains.RegIs.of_saved hS₁₂ rfl (Chains.regIs_reg hm₁₁ rfl g12)
  have g15 := Chains.RegIs.of_saved hS₁₂ rfl (Chains.regIs_reg hm₁₁ rfl g15)
  have gbp := Chains.RegIs.of_saved hS₁₂ rfl (Chains.regIs_reg hm₁₁ rfl gbp)
  have gbx := Chains.RegIs.of_saved hS₁₂ rfl (Chains.regIs_reg hm₁₁ rfl gbx)
  have g14 := Chains.RegIs.of_saved hS₁₂ rfl (Chains.regIs_reg hm₁₁ rfl g14)
  -- b64: the scratch pointers, the nodes from height zero
  have hwf₁₂ := r.frame_wf hpre hK₁₂.1.2.2.2 (fun _ ↦ 0) 0
  refine Chains.blk r hp b64_in_code (j := NativeRustcX64.Sphincs.SphincsVerify.b64Offset) (List.cons_ne_nil _ _) run_b64 hwf₁₂
    (fun _ h ↦ nomatch h) (match_frameS hpre hK₁₂.1 (k := []) trivial) fun st₁₃ hm₁₃ hpc₁₃ ↦ ?_
  refine Chains.pc_at hpc₁₃ (cont _ ⟨Keep.of_block hpre hK₁₂ hm₁₃ hwf₁₂ (by decide +kernel) rfl,
    by decide, Chains.regIs_lit hm₁₃ rfl, Chains.regIs_ptr hm₁₃ rfl,
    (hm₁₃.regs .r15 _ rfl).trans g12, ?_, ?_, ?_, ?_,
    Chains.regIs_reg hm₁₃ rfl gbx, Chains.regIs_reg hm₁₃ rfl g14⟩)
  · rw [show reg st₁₃.data .r13 = reg m .r13 from Chains.regIs_reg hm₁₃ rfl g15]
    exact h15
  · rw [show reg st₁₃.data .rbp = reg m .rbp from Chains.regIs_reg hm₁₃ rfl gbp]
    exact hbp
  · exact r.bytesAt_kept hpre hm₁₃ hwf₁₂ (by flen) g13
      (by rw [NativeRustc.length_wordBytes]; decide +kernel)
  · have hD' := Chains.take_of_bytesAt hD 16
    have e : r.forsUpTo c 0 = (Keccak.hashBytes ((r.seed ++ forsNodeAdrs r.idx c 0 (r.leafOf c)) ++
        (r.openingOf c).secret)).take 16 := rfl
    rw [← e] at hD'
    have hl := r.length_forsUpTo c 0
    exact r.bytesAt_kept hpre hm₁₃ hwf₁₂ (by rw [hl]; omega) hD' (by rw [hl]; decide +kernel)

end

end NativeRustcX64.SphincsVerifyProof.Fors
