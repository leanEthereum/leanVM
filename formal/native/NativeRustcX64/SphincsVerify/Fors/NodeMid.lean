module

public import NativeRustcX64.SphincsVerify.Fors.NodeHead

/-!
# A FORS node, its middle: the absorbs and the clone (x86-64)

From `N1` at `b66` (directive 763): `b66` puts `PK.seed` in hasher A's buffer (its `buf_len` 0 to
16), `b69`, `b72 .. b74` copy the node's address after it (`memcpy`); `b75`, `b71` (its `buf_len`
48), `b79` clone A into hasher B (`memcpy`); `b80`, `b83 .. b85` copy the children after B's 48
bytes (`memcpy`); `b86`, `b82` (B's `buf_len` 80), `b90` copy B's zero state into A (`memcpy`):
`N2` at `b91`, B's buffer holding `PK.seed | ADRS | children` (**`node_mid`**).
-/

namespace NativeRustcX64.SphincsVerifyProof.Fors

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym LeanVM.Protocol.KeccakHash
open NativeRustcX64.Sphincs.SphincsVerify

@[expose] public section

/-- **At `b91`**: R13 B's `buf_len` (80), R15 the final block, R12 hasher A; A's state zero, B's
buffer `PK.seed | ADRS | children`. -/
structure N2 [Labels] (r : Run) (c z : Nat) (m : MachineData) : Prop where
  keep : Keep r c m
  hz : z < 10
  w64 : r.WordAt m 56 (z + 1).toUInt64
  w104 : r.WordAt m 88 c.toUInt64
  r13 : Run.RegIs m .r13 (BitVec.ofNat 64 80)
  r15 : Run.RegIs m .r12 (r.off 2056)
  r12 : Run.RegIs m .r15 (r.off 4104)
  a0 : BytesAt m.dmem (r.off 4104) (List.replicate 200 0)
  t : BytesAt m.dmem (r.off 760) (r.seed ++ r.nodeAdrsOf c z ++ r.childrenOf c z)
  r14 : Run.RegIs m .r14 (Labels.label "memcpy").toBitVec

end

public section

variable {r : Run}

theorem zeros_slice {d : DataMem} {o n a k : Nat} (h : BytesAt d (r.off o) (List.replicate n 0))
    (hk : a + k ≤ n) : BytesAt d (r.off (o + a)) (List.replicate k 0) := by
  have := Chains.BytesAt.slice h a k
  rwa [Run.off_add, List.drop_replicate, List.take_replicate, Nat.min_eq_left (by omega)] at this

theorem bytes_lit0 : (List.range 8).map (byteOf (BitVec.ofNat 64 0)) = List.replicate 8 0 := by
  decide

variable [Host]

/-- **A node's middle**: from `N1 r c z` at `b66`, `N2 r c z` at `b91`. -/
theorem node_mid (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {c z : Nat} {m : MachineData} (h : N1 r c z m) {R : MachineState → Prop}
    (cont : ∀ m', N2 r c z m' → Eventually (step1 Host.exe) R ⟨m', r.pc NativeRustcX64.Sphincs.SphincsVerify.b91Offset⟩) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b66Offset⟩ := by
  obtain ⟨hK, hz, w64, w104, h12, hblock, ha0, hch, had, h14⟩ := h
  have hc24 := hK.2.1.hc
  have hadl : (r.nodeAdrsOf c z).length = 32 := length_forsNodeAdrs _ _ _ _
  have hchl := r.length_childrenOf hc24 hz
  have hsl := Digest.length_seed r
  -- b66, b69, b72 .. b74: `PK.seed` into A's buffer, the address's `memcpy`
  have hwf := r.frame_wf hpre hK.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b75Offset).toBitVec
  have hm := match_litS hpre hK.1 (ret := (r.pc NativeRustcX64.Sphincs.SphincsVerify.b75Offset).toBitVec)
    (k := [(.r12, .ptr 0 2056), (.r14, .label "memcpy")]) ⟨Chains.known_ptr hblock, h14, trivial⟩ (o := 4440) (v := 0)
    (by rw [bytes_lit0]; exact zeros_slice ha0 (a := 336) (k := 8) (by omega))
  refine Chains.blk r hp b66_in_code (List.cons_ne_nil _ _) run_b66 hwf (fun _ h ↦ nomatch h) hm
    fun st₁ hm₁ hpc₁ ↦ ?_
  refine Chains.pc_at ((Chains.pc_true hpc₁).trans (Chains.labelAt r hp b69_in_code rfl)) ?_
  refine Chains.blk r hp b69_in_code (List.cons_ne_nil _ _) (exec_after run_b66 run_b69) hwf
    (fun _ h ↦ nomatch h) hm₁ fun st₂ hm₂ hpc₂ ↦ ?_
  refine Chains.pc_at (hpc₂.trans (Chains.labelAt r hp b72_in_code rfl)) ?_
  refine Chains.blk r hp b72_in_code (List.cons_ne_nil _ _) (exec_after run_b69 run_b72) hwf
    (fun _ h ↦ nomatch h) hm₂ fun st₃ hm₃ hpc₃ ↦ ?_
  refine Chains.pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b73Offset) (Chains.pc_false hpc₃) ?_
  refine Chains.blk r hp b73_in_code (List.cons_ne_nil _ _) (exec_after run_b72 run_b73) hwf
    (fun _ h ↦ nomatch h) hm₃ fun st₄ hm₄ hpc₄ ↦ ?_
  refine Chains.pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b74Offset) (Chains.pc_false hpc₄) ?_
  refine Chains.blk r hp b74_in_code (List.cons_ne_nil _ _) (exec_after run_b73 run_b74) hwf
    (fun _ _ ↦ rfl) hm₄ fun st₅ hm₅ hpc₅ ↦ ?_
  have kept₅ : KeptBy r _ m st₅.data := keptBy_of_match hpre hm₅ hwf
  have gseed : BytesAt st₅.data.dmem (r.off 4304) r.seed :=
    Chains.frame_copy16 hm₅ (o := 4304) (o' := 112) (by decide) (by decide +kernel)
      (by decide +kernel) hsl hK.seed
  have g16 := Chains.frame_write_val hm₅ (o := 4440) (n := 8) (v := .lit 16) (by decide)
    (by decide +kernel)
  have ga0 := kept₅ (by flen) (by rw [List.length_replicate]; decide +kernel)
    (zeros_slice ha0 (a := 0) (k := 200) (by omega))
  refine memcpy_then hpre hc hpc₅ (KeepC.of_block hpre hK hm₅ hwf (by decide +kernel) rfl)
    (a := 4320) (b := 3080) (n := 32) (Chains.regIs_ptr hm₅ rfl) (Chains.regIs_ptr hm₅ rfl)
    (Chains.toNat_of_lit hm₅ rfl (by decide)) (by decide) (by decide) (by decide) hadl
    (kept₅ (by rw [hadl]; omega) (by rw [hadl]; decide +kernel) had)
    fun m₆ hK₆ hS₆ hkc₆ had₆ ↦ ?_
  have r15 : Run.RegIs m₆ .r12 (r.off 2056) :=
    Chains.RegIs.of_saved hS₆ rfl (Chains.regIs_ptr hm₅ rfl)
  have r12 := Chains.RegIs.of_saved hS₆ rfl (Chains.regIs_reg hm₅ rfl h12)
  have h14 := Chains.RegIs.of_saved hS₆ rfl (Chains.regIs_label (y := .r14) hm₅ rfl)
  have g64 := hkc₆ (by flen) (by flen) (kept₅ (by flen)
    (by rw [NativeRustc.length_wordBytes]; decide +kernel) w64)
  have g104 := hkc₆ (by flen) (by flen) (kept₅ (by flen)
    (by rw [NativeRustc.length_wordBytes]; decide +kernel) w104)
  have gch := hkc₆ (by rw [hchl]; omega) (by rw [hchl]; omega)
    (kept₅ (by rw [hchl]; omega) (by rw [hchl]; decide +kernel) hch)
  have gsa : BytesAt m₆.dmem (r.off 4304) (r.seed ++ r.nodeAdrsOf c z) :=
    Chains.BytesAt.cat (hkc₆ (by rw [hsl]; omega) (by rw [hsl]; omega) gseed) had₆
      (by rw [hsl])
  have g16 := hkc₆ (by flen) (by flen) g16
  have ga0 := hkc₆ (by flen) (by flen) ga0
  -- b75, b71, b79: A's `buf_len` 48, the clone into B
  have hwf₆ := r.frame_wf hpre hK₆.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b80Offset).toBitVec
  have hm₆ := match_litS hpre hK₆.1 (ret := (r.pc NativeRustcX64.Sphincs.SphincsVerify.b80Offset).toBitVec)
    (k := [(.rbx, .lit 32), (.r13, .lit 32), (.rbp, .ptr 0 3080), (.r15, .ptr 0 4104),
      (.r14, .label "memcpy")])
    ⟨Chains.known_lit (Chains.RegIs.of_saved hS₆ rfl (Chains.regIs_lit hm₅ rfl)),
      Chains.known_lit (Chains.RegIs.of_saved hS₆ rfl (Chains.regIs_lit hm₅ rfl)),
      Chains.known_ptr (Chains.RegIs.of_saved hS₆ rfl (Chains.regIs_ptr hm₅ rfl)),
      Chains.known_ptr r12, h14, trivial⟩ g16
  refine Chains.blk r hp b75_in_code (List.cons_ne_nil _ _) run_b75 hwf₆ (fun _ h ↦ nomatch h) hm₆
    fun st₇ hm₇ hpc₇ ↦ ?_
  refine Chains.pc_at ((Chains.pc_true hpc₇).trans (Chains.labelAt r hp b71_in_code rfl)) ?_
  refine Chains.blk r hp b71_in_code (List.cons_ne_nil _ _) (exec_after run_b75 run_b71) hwf₆
    (fun _ h ↦ nomatch h) hm₇ fun st₈ hm₈ hpc₈ ↦ ?_
  refine Chains.pc_at ((Chains.pc_true hpc₈).trans (Chains.labelAt r hp b79_in_code rfl)) ?_
  refine Chains.blk r hp b79_in_code (List.cons_ne_nil _ _) (exec_after run_b71 run_b79) hwf₆
    (fun _ _ ↦ rfl) hm₈ fun st₉ hm₉ hpc₉ ↦ ?_
  have kept₉ : KeptBy r _ m₆ st₉.data := keptBy_of_match hpre hm₉ hwf₆
  have g48 := Chains.frame_write_val hm₉ (o := 4440) (n := 8) (v := .lit 48) (by decide)
    (by decide +kernel)
  have gsa := kept₉ (by rw [List.length_append, hsl, hadl]; omega)
    (by rw [List.length_append, hsl, hadl]; decide +kernel) gsa
  have ga0 := kept₉ (by flen) (by rw [List.length_replicate]; decide +kernel) ga0
  refine memcpy_then' hpre hc hpc₉ (KeepC.of_block hpre hK₆ hm₉ hwf₆ (by decide +kernel) rfl)
    (a := 560) (b := 4104) (n := 344) (Chains.regIs_ptr hm₉ rfl) (Chains.regIs_ptr hm₉ rfl)
    (Chains.toNat_of_lit hm₉ rfl (by decide)) (by decide) (by decide) (by decide)
    fun m₁₀ hK₁₀ hS₁₀ hkc₁₀ hB₁₀ ↦ ?_
  have r15 := Chains.RegIs.of_saved hS₁₀ rfl (Chains.regIs_reg hm₉ rfl r15)
  have h14 := Chains.RegIs.of_saved hS₁₀ rfl (Chains.regIs_label (y := .r14) hm₉ rfl)
  have g64 := hkc₁₀ (by flen) (by flen) (kept₉ (by flen)
    (by rw [NativeRustc.length_wordBytes]; decide +kernel) g64)
  have g104 := hkc₁₀ (by flen) (by flen) (kept₉ (by flen)
    (by rw [NativeRustc.length_wordBytes]; decide +kernel) g104)
  have gch := hkc₁₀ (by rw [hchl]; omega) (by rw [hchl]; omega)
    (kept₉ (by rw [hchl]; omega) (by rw [hchl]; decide +kernel) gch)
  have gB0 := Chains.copy_slice (c := 0) hB₁₀ (by flen) ga0
  have gBsa := Chains.copy_slice (c := 200) hB₁₀ (by rw [List.length_append, hsl, hadl]; omega) gsa
  have gB48 := Chains.copy_slice (c := 336) hB₁₀ (by flen) g48
  -- b80, b83 .. b85: the children into B's buffer
  have hwf₁₀ := r.frame_wf hpre hK₁₀.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b86Offset).toBitVec
  have hm₁₀ := match_litS hpre hK₁₀.1 (ret := (r.pc NativeRustcX64.Sphincs.SphincsVerify.b86Offset).toBitVec)
    (k := [(.r14, .label "memcpy")]) ⟨h14, trivial⟩ gB48
  refine Chains.blk r hp b80_in_code (List.cons_ne_nil _ _) run_b80 hwf₁₀ (fun _ h ↦ nomatch h)
    hm₁₀ fun st₁₁ hm₁₁ hpc₁₁ ↦ ?_
  refine Chains.pc_at (hpc₁₁.trans (Chains.labelAt r hp b83_in_code rfl)) ?_
  refine Chains.blk r hp b83_in_code (List.cons_ne_nil _ _) (exec_after run_b80 run_b83) hwf₁₀
    (fun _ h ↦ nomatch h) hm₁₁ fun st₁₂ hm₁₂ hpc₁₂ ↦ ?_
  refine Chains.pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b84Offset) (Chains.pc_false hpc₁₂) ?_
  refine Chains.blk r hp b84_in_code (List.cons_ne_nil _ _) (exec_after run_b83 run_b84) hwf₁₀
    (fun _ h ↦ nomatch h) hm₁₂ fun st₁₃ hm₁₃ hpc₁₃ ↦ ?_
  refine Chains.pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b85Offset) (Chains.pc_false hpc₁₃) ?_
  refine Chains.blk r hp b85_in_code (List.cons_ne_nil _ _) (exec_after run_b84 run_b85) hwf₁₀
    (fun _ _ ↦ rfl) hm₁₃ fun st₁₄ hm₁₄ hpc₁₄ ↦ ?_
  have kept₁₄ : KeptBy r _ m₁₀ st₁₄.data := keptBy_of_match hpre hm₁₄ hwf₁₀
  refine memcpy_then hpre hc hpc₁₄ (KeepC.of_block hpre hK₁₀ hm₁₄ hwf₁₀ (by decide +kernel) rfl)
    (a := 808) (b := 19144) (n := 32) (Chains.regIs_ptr hm₁₄ rfl) (Chains.regIs_ptr hm₁₄ rfl)
    (Chains.toNat_of_lit hm₁₄ rfl (by decide)) (by decide) (by decide) (by decide) hchl
    (kept₁₄ (by rw [hchl]; omega) (by rw [hchl]; decide +kernel) gch)
    fun m₁₅ hK₁₅ hS₁₅ hkc₁₅ hch₁₅ ↦ ?_
  have r15 := Chains.RegIs.of_saved hS₁₅ rfl (Chains.regIs_reg hm₁₄ rfl r15)
  have h14 := Chains.RegIs.of_saved hS₁₅ rfl (Chains.regIs_label (y := .r14) hm₁₄ rfl)
  have g64 := hkc₁₅ (by flen) (by flen) (kept₁₄ (by flen)
    (by rw [NativeRustc.length_wordBytes]; decide +kernel) g64)
  have g104 := hkc₁₅ (by flen) (by flen) (kept₁₄ (by flen)
    (by rw [NativeRustc.length_wordBytes]; decide +kernel) g104)
  have gB0 := hkc₁₅ (by flen) (by flen)
    (kept₁₄ (by flen) (by rw [List.length_replicate]; decide +kernel) gB0)
  have gBsa := hkc₁₅ (by rw [List.length_append, hsl, hadl]; omega)
    (by rw [List.length_append, hsl, hadl]; omega)
    (kept₁₄ (by rw [List.length_append, hsl, hadl]; omega)
      (by rw [List.length_append, hsl, hadl]; decide +kernel) gBsa)
  have g912 := Chains.frame_write_val hm₁₄ (o := 896) (n := 8) (v := .lit 48) (by decide)
    (by decide +kernel)
  have g912 := hkc₁₅ (by flen) (by flen) g912
  have gT : BytesAt m₁₅.dmem (r.off 760) (r.seed ++ r.nodeAdrsOf c z ++ r.childrenOf c z) :=
    Chains.BytesAt.cat gBsa hch₁₅ (by rw [List.length_append, hsl, hadl])
  have hTl : (r.seed ++ r.nodeAdrsOf c z ++ r.childrenOf c z).length = 80 := by
    rw [List.length_append, List.length_append, hsl, hadl, hchl]
  -- b86, b82, b90: B's `buf_len` 80, B's zero state into A
  have hwf₁₅ := r.frame_wf hpre hK₁₅.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b91Offset).toBitVec
  have hm₁₅ := match_litS hpre hK₁₅.1 (ret := (r.pc NativeRustcX64.Sphincs.SphincsVerify.b91Offset).toBitVec)
    (k := [(.rbx, .lit 32), (.r15, .lit 32), (.rbp, .ptr 0 19144), (.r14, .label "memcpy")])
    ⟨Chains.known_lit (Chains.RegIs.of_saved hS₁₅ rfl (Chains.regIs_lit hm₁₄ rfl)),
      Chains.known_lit (Chains.RegIs.of_saved hS₁₅ rfl (Chains.regIs_lit hm₁₄ rfl)),
      Chains.known_ptr (Chains.RegIs.of_saved hS₁₅ rfl (Chains.regIs_ptr hm₁₄ rfl)), h14, trivial⟩ g912
  refine Chains.blk r hp b86_in_code (List.cons_ne_nil _ _) run_b86 hwf₁₅ (fun _ h ↦ nomatch h)
    hm₁₅ fun st₁₆ hm₁₆ hpc₁₆ ↦ ?_
  refine Chains.pc_at ((Chains.pc_true hpc₁₆).trans (Chains.labelAt r hp b82_in_code rfl)) ?_
  refine Chains.blk r hp b82_in_code (List.cons_ne_nil _ _) (exec_after run_b86 run_b82) hwf₁₅
    (fun _ h ↦ nomatch h) hm₁₆ fun st₁₇ hm₁₇ hpc₁₇ ↦ ?_
  refine Chains.pc_at ((Chains.pc_true hpc₁₇).trans (Chains.labelAt r hp b90_in_code rfl)) ?_
  refine Chains.blk r hp b90_in_code (List.cons_ne_nil _ _) (exec_after run_b82 run_b90) hwf₁₅
    (fun _ _ ↦ rfl) hm₁₇ fun st₁₈ hm₁₈ hpc₁₈ ↦ ?_
  have kept₁₈ : KeptBy r _ m₁₅ st₁₈.data := keptBy_of_match hpre hm₁₈ hwf₁₅
  have gT := kept₁₈ (by rw [hTl]; omega) (by rw [hTl]; decide +kernel) gT
  refine memcpy_then hpre hc hpc₁₈ (KeepC.of_block hpre hK₁₅ hm₁₈ hwf₁₅ (by decide +kernel) rfl)
    (a := 4104) (b := 560) (n := 200) (Chains.regIs_ptr hm₁₈ rfl) (Chains.regIs_ptr hm₁₈ rfl)
    (Chains.toNat_of_lit hm₁₈ rfl (by decide)) (by decide) (by decide) (by decide)
    (List.length_replicate ..)
    (kept₁₈ (by flen) (by rw [List.length_replicate]; decide +kernel) gB0)
    fun m₁₉ hK₁₉ hS₁₉ hkc₁₉ hA₁₉ ↦
      cont m₁₉ ⟨hK₁₉, hz,
        hkc₁₉ (by flen) (by flen) (kept₁₈ (by flen)
    (by rw [NativeRustc.length_wordBytes]; decide +kernel) g64),
        hkc₁₉ (by flen) (by flen) (kept₁₈ (by flen)
    (by rw [NativeRustc.length_wordBytes]; decide +kernel) g104),
        Chains.RegIs.of_saved hS₁₉ rfl (Chains.regIs_lit hm₁₈ rfl),
        Chains.RegIs.of_saved hS₁₉ rfl (Chains.regIs_reg hm₁₈ rfl r15),
        Chains.RegIs.of_saved hS₁₉ rfl (Chains.regIs_ptr hm₁₈ rfl), hA₁₉,
        hkc₁₉ (by rw [hTl]; omega) (by rw [hTl]; omega) gT,
        Chains.RegIs.of_saved hS₁₉ rfl (Chains.regIs_label (y := .r14) hm₁₈ rfl)⟩

end

end NativeRustcX64.SphincsVerifyProof.Fors
