module

public import NativeRustcX64.SphincsVerify.Parse.Layer2

/-!
# The parse, part 6: the parsed signature assembled (`b29 .. b33`, x86-64)

`b29` copies the randomizer (`sigPtr + 0`, 16 bytes) to `17420` (R13 its address) and `memcpy`s
the openings (`4072`) to `12780`; `b30` stores layer 0's chain address (`17436`) at `184` and
`memcpy`s its chain values (`9320`) to `17436`; `b31` stores layer 0's counter at `18460` and
`memcpy`s layer 1's chain values (`8296`) to `18464`; `b32` copies layer 1's counter (`16`) to
`19488` and `memcpy`s layer 2's chain values (`10344`) to `19492`; `b33` stores layer 2's counter
at `20516` and `memcpy`s the paths (`1592`) to `17004`. Result at `b34`: `A5`, R13 `17420`,
RBP `memcpy`.
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustc.Sphincs.ParseMem NativeRustcX64.Sym
  NativeRustcX64.Sphincs.SphincsVerify LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The `n` bytes at `o` of region `r` are the low bytes of `v`. -/
def holdsVal (ws : List Write) (r o n : Nat) (v : Sym) : Bool :=
  (List.range n).all fun i => findWrite r (o + i) ws == some (v, i)

/-- After `b29`: the randomizer at `17420`, the openings at `12780`. -/
def A1 (r : Run) : List (Nat × Nat × List UInt8) :=
  L3 r ++ [(17420, 16, slice r.sigB 0 16), (12780, 4224, opens r)]

/-- After `b30`: layer 0's chain address at `184`, its chain values at `17436`. -/
def A2 (r : Run) : List (Nat × Nat × List UInt8) :=
  A1 r ++ [(184, 8, wordBytes (r.addr 17436)), (17436, 1024, slice r.sigB 4244 1024)]

/-- After `b31`: layer 0's counter at `18460`, layer 1's chain values at `18464`. -/
def A3 (r : Run) : List (Nat × Nat × List UInt8) :=
  A2 r ++ [(18460, 4, (slice r.sigB 4240 4).reverse), (18464, 1024, slice r.sigB 5400 1024)]

/-- After `b32`: layer 1's counter at `19488`, layer 2's chain values at `19492`. -/
def A4 (r : Run) : List (Nat × Nat × List UInt8) :=
  A3 r ++ [(19488, 4, (slice r.sigB 5396 4).reverse), (19492, 1024, slice r.sigB 6556 1024)]

/-- After `b33`: layer 2's counter at `20516`, the paths at `17004`. -/
def A5 (r : Run) : List (Nat × Nat × List UInt8) :=
  A4 r ++ [(20516, 4, (slice r.sigB 6552 4).reverse), (17004, 416, pbytesB r.sigB)]

end

public section

/-- Decides the assembly's facts' checks. -/
macro "facts_dec4" : tactic => `(tactic| (
  simp only [A5, A4, A3, A2, A1, L3, L2p, L2, L1, L0c, L0, base3, List.cons_append, List.nil_append,
    List.singleton_append, List.append_assoc]
  facts_dec))

/-- **A value stored**: its low bytes. -/
theorem bytesAt_val [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r o n : Nat} {B : BitVec 64} {sz : Nat} (hb : env.regions[r]? = some (B, sz))
    (hle : o + n ≤ sz) {v : Sym} (hc : holdsVal S.mem r o n v = true) :
    BytesAt m.dmem (B + BitVec.ofNat 64 o) ((List.range n).map (byteOf (v.eval env))) :=
  hm.bytesAt_write hb hle fun i hi ↦ by
    have := List.all_eq_true.mp hc i (List.mem_range.mpr hi)
    exact beq_iff_eq.mp this

theorem length_opens (r : Run) : (opens r).length = 4224 := length_openingsB r.hsig le_rfl

/-- Facts extended by two. -/
theorem Facts.snoc2 {r : Run} {d : DataMem} {L : List (Nat × Nat × List UInt8)} (h : Facts r d L)
    {o n o' n' : Nat} {bs bs' : List UInt8} (h1 : bs.length = n ∧ BytesAt d (r.off o) bs)
    (h2 : bs'.length = n' ∧ BytesAt d (r.off o') bs') :
    Facts r d (L ++ [(o, n, bs), (o', n', bs')]) := by
  rw [facts_append]
  exact ⟨h, h1, h2, trivial⟩

theorem mem_A1 (r : Run) : (4072, 4224, opens r) ∈ L3 r := by simp [L3, L2p, L2, L1, L0c, L0]

variable (r : Run) [ElfHost]

/-- **`b29 .. b33`**: the parsed signature assembled. -/
theorem assemble_spec (hp : PlacedIn code r.sec r.k) (hpre : r.Pre) (hc : Callees) {m : MachineData}
    (h : LS3 r m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc b34Offset ∧ r.Frame st.data ∧
      Facts r st.data.dmem (A5 r) ∧ Run.RegIs st.data .r13 (r.off 17420) ∧
      Run.RegIs st.data .rbp (Labels.label "memcpy").toBitVec) ⟨m, r.pc b29Offset⟩ := by
  obtain ⟨hF, hL, hbx, h14, h12, h15, hbp⟩ := h
  have hl4 : ∀ k, k + 4 ≤ 7740 → (slice r.sigB k 4).reverse.length = 4 := fun k hk ↦ by
    rw [List.length_reverse, length_slice (by rw [r.hsig]; omega)]
  -- `b29`: randomizer to `17420`, openings to `12780`
  refine memcpy_block_sig r hp hpre hc b29_in_code (jn := b30Offset) rfl run_b29 (by decide) rfl hF hbx
    ⟨hbp, trivial⟩ (a := 12780) (s := 4072) (n := 4224) (by decide) (by decide) (by decide) fun m₁ hm₁ ↦
    ⟨regIs_ptr0 r rfl hm₁ rfl, regIs_ptr0 r rfl hm₁ rfl, rdx_lit hm₁ rfl (by decide),
      fun m₂ hF₂ hS hB hout hc₁ ↦ ?_⟩
  have hrand : BytesAt m₁.dmem (r.off 17420) (slice r.sigB 0 16) :=
    copy hm₁ (r := 0) (o := 17420) (r' := 4) (o' := 0) (n := 16) rfl (by decide) (by decide)
      (length_slice (by rw [r.hsig]; decide))
      (by simpa [Env.base, regsSig, Run.frameRegs] using sig_slice r hpre hF.2.2.1 (k := 0) (n := 16) (by decide))
  have hL₁ := Facts.of_block r rfl hm₁ hL (by facts_dec4)
  have ho₁ := bytesAt_of_block r rfl hm₁ (hL.get (mem_A1 r)) (N := 4224) (by decide)
    (le_of_eq (length_opens r)) (by decide)
  have hA1 : Facts r m₂.dmem (A1 r) := Facts.snoc2
    (Facts.of_call r hpre hc₁ (by decide) (Nat.zero_le _) hout hL₁ (by facts_dec4))
    ⟨length_slice (by rw [r.hsig]; decide), r.bytesAt_of_call hpre hc₁ (by decide) (Nat.zero_le _) hout
      (by rw [length_slice (by rw [r.hsig]; decide)]; decide)
      (by right; decide) hrand⟩
    ⟨length_opens r, by rwa [← length_opens r, bytesOf_of_bytesAt ho₁] at hB⟩
  have h13₂ := regIs_saved hS rfl (regIs_ptr0 r rfl hm₁ (y := .r13) rfl)
  have h12₂ := low4_saved hS rfl (h12.of_eq (hm₁.regs .r12 _ rfl))
  have h15₂ := low4_saved hS rfl (h15.of_eq (hm₁.regs .r15 _ rfl))
  have h14₂ := regIs_saved hS rfl ((hm₁.regs .r14 _ rfl).trans h14)
  have hbp₂ := regIs_saved hS rfl (hm₁.regs .rbp _ rfl : Run.RegIs m₁ .rbp (Labels.label "memcpy").toBitVec)
  -- `b30`: layer 0 chain address at `184`, its chain values to `17436`
  refine memcpy_block r hp hpre hc b30_in_code (jn := b31Offset) rfl run_b30 (by decide) rfl hF₂ ⟨hbp₂, trivial⟩
    trivial (a := 17436) (s := 9320) (n := 1024) (by decide) (by decide) (by decide) fun m₃ hm₃ ↦
    ⟨regIs_ptr0 r rfl hm₃ rfl, regIs_ptr0 r rfl hm₃ rfl, rdx_lit hm₃ rfl (by decide),
      fun m₄ hF₄ hS₄ hB₄ hout₄ hc₃ ↦ ?_⟩
  have h184 : BytesAt m₃.dmem (r.off 184) (wordBytes (r.addr 17436)) := by
    have := bytesAt_val hm₃ (r := 0) (o := 184) (n := 8) (v := .ptr 0 17436) rfl (by decide) (by decide)
    have e : Sym.eval (r.env m₂ (fun _ ↦ 0) (r.pc b31Offset).toBitVec) (.ptr 0 (17436 : Nat)) =
        r.off 17436 := eval_base r rfl 17436
    rw [show ((17436 : Nat) : Int) = 17436 from rfl] at e
    rw [e] at this
    have h2 : (List.range 8).map (byteOf (r.off 17436)) = wordBytes (r.addr 17436) :=
      regBytes_eq_wordBytes (r.off 17436)
    rwa [h2] at this
  have hL₃ := Facts.of_block r rfl hm₃ hA1 (by facts_dec4)
  have hcv₃ := bytesAt_of_block r rfl hm₃ (hA1.get (o := 9320) (n := 1024)
    (bs := slice r.sigB 4244 1024) (by simp [A1, L3, L2p, L2, L1]))
    (N := 1024) (by decide) (le_of_eq (length_slice (by rw [r.hsig]; decide))) (by decide)
  have hA2 : Facts r m₄.dmem (A2 r) := Facts.snoc2
    (Facts.of_call r hpre hc₃ (by decide) (Nat.zero_le _) hout₄ hL₃ (by facts_dec4))
    ⟨length_wordBytes _, r.bytesAt_of_call hpre hc₃ (by decide) (Nat.zero_le _) hout₄
      (by rw [length_wordBytes]; decide) (by left; rw [length_wordBytes]; decide) h184⟩
    ⟨length_slice (by rw [r.hsig]; decide), by
      rwa [← length_slice (by rw [r.hsig]; decide : 4244 + 1024 ≤ r.sigB.length), bytesOf_of_bytesAt hcv₃] at hB₄⟩
  have h13₄ := regIs_saved hS₄ rfl ((hm₃.regs .r13 _ rfl).trans h13₂)
  have h12₄ := low4_saved hS₄ rfl (h12₂.of_eq (hm₃.regs .r12 _ rfl))
  have h15₄ := low4_saved hS₄ rfl (h15₂.of_eq (hm₃.regs .r15 _ rfl))
  have h14₄ := regIs_saved hS₄ rfl ((hm₃.regs .r14 _ rfl).trans h14₂)
  have hbp₄ := regIs_saved hS₄ rfl (hm₃.regs .rbp _ rfl : Run.RegIs m₃ .rbp (Labels.label "memcpy").toBitVec)
  -- `b31`: layer 0 counter at `18460`, layer 1 chain values to `18464`
  refine memcpy_block r hp hpre hc b31_in_code (jn := b32Offset) rfl run_b31 (by decide) rfl hF₄ ⟨hbp₄, trivial⟩
    trivial (a := 18464) (s := 8296) (n := 1024) (by decide) (by decide) (by decide) fun m₅ hm₅ ↦
    ⟨regIs_ptr0 r rfl hm₅ rfl, regIs_ptr0 r rfl hm₅ rfl, rdx_lit hm₅ rfl (by decide),
      fun m₆ hF₆ hS₆ hB₆ hout₆ hc₅ ↦ ?_⟩
  have hc0 : BytesAt m₅.dmem (r.off 18460) (slice r.sigB 4240 4).reverse :=
    bytesAt_low hm₅ (r := 0) (o := 18460) (sz := 21632)
      (v := .un .trunc .W32 (.reg .r12)) rfl (by decide) (by decide) h12₄.trunc
  have hL₅ := Facts.of_block r rfl hm₅ hA2 (by facts_dec4)
  have hcv₅ := bytesAt_of_block r rfl hm₅ (hA2.get (o := 8296) (n := 1024)
    (bs := slice r.sigB 5400 1024) (by simp [A2, A1, L3, L2p, L2]))
    (N := 1024) (by decide) (le_of_eq (length_slice (by rw [r.hsig]; decide))) (by decide)
  have hA3 : Facts r m₆.dmem (A3 r) := Facts.snoc2
    (Facts.of_call r hpre hc₅ (by decide) (Nat.zero_le _) hout₆ hL₅ (by facts_dec4))
    ⟨hl4 4240 (by decide), r.bytesAt_of_call hpre hc₅ (by decide) (Nat.zero_le _) hout₆
      (by rw [hl4 4240 (by decide)]; decide) (by left; rw [hl4 4240 (by decide)]) hc0⟩
    ⟨length_slice (by rw [r.hsig]; decide), by
      rwa [← length_slice (by rw [r.hsig]; decide : 5400 + 1024 ≤ r.sigB.length), bytesOf_of_bytesAt hcv₅] at hB₆⟩
  have h13₆ := regIs_saved hS₆ rfl ((hm₅.regs .r13 _ rfl).trans h13₄)
  have h15₆ := low4_saved hS₆ rfl (h15₄.of_eq (hm₅.regs .r15 _ rfl))
  have h14₆ := regIs_saved hS₆ rfl ((hm₅.regs .r14 _ rfl).trans h14₄)
  have hbp₆ := regIs_saved hS₆ rfl (hm₅.regs .rbp _ rfl : Run.RegIs m₅ .rbp (Labels.label "memcpy").toBitVec)
  -- `b32`: layer 1 counter from `16` to `19488`, layer 2 chain values to `19492`
  refine memcpy_block r hp hpre hc b32_in_code (jn := b33Offset) rfl run_b32 (by decide) rfl hF₆
    ⟨h14₆.trans (eval_base r rfl 10344).symm, hbp₆, trivial⟩ trivial (a := 19492) (s := 10344)
    (n := 1024) (by decide) (by decide) (by decide) fun m₇ hm₇ ↦
    ⟨regIs_ptr0 r rfl hm₇ rfl, regIs_ptr0 r rfl hm₇ rfl, rdx_lit hm₇ rfl (by decide),
      fun m₈ hF₈ hS₈ hB₈ hout₈ hc₇ ↦ ?_⟩
  have hc1 : BytesAt m₇.dmem (r.off 19488) (slice r.sigB 5396 4).reverse :=
    copy hm₇ (r := 0) (o := 19488) (r' := 0) (o' := 16) (n := 4) rfl (by decide) (by decide)
      (hl4 5396 (by decide)) (hA3.get (o := 16) (n := 4) (by simp [A3, A2, A1, L3, L2p]))
  have hL₇ := Facts.of_block r rfl hm₇ hA3 (by facts_dec4)
  have hcv₇ := bytesAt_of_block r rfl hm₇ (hA3.get (o := 10344) (n := 1024)
    (bs := slice r.sigB 6556 1024) (by simp [A3, A2, A1, L3]))
    (N := 1024) (by decide) (le_of_eq (length_slice (by rw [r.hsig]; decide))) (by decide)
  have hA4 : Facts r m₈.dmem (A4 r) := Facts.snoc2
    (Facts.of_call r hpre hc₇ (by decide) (Nat.zero_le _) hout₈ hL₇ (by facts_dec4))
    ⟨hl4 5396 (by decide), r.bytesAt_of_call hpre hc₇ (by decide) (Nat.zero_le _) hout₈
      (by rw [hl4 5396 (by decide)]; decide) (by left; rw [hl4 5396 (by decide)]) hc1⟩
    ⟨length_slice (by rw [r.hsig]; decide), by
      rwa [← length_slice (by rw [r.hsig]; decide : 6556 + 1024 ≤ r.sigB.length), bytesOf_of_bytesAt hcv₇] at hB₈⟩
  have h13₈ := regIs_saved hS₈ rfl ((hm₇.regs .r13 _ rfl).trans h13₆)
  have h15₈ := low4_saved hS₈ rfl (h15₆.of_eq (hm₇.regs .r15 _ rfl))
  have hbp₈ := regIs_saved hS₈ rfl (hm₇.regs .rbp _ rfl : Run.RegIs m₇ .rbp (Labels.label "memcpy").toBitVec)
  -- `b33`: layer 2 counter at `20516`, paths to `17004`
  have hpaths : BytesAt m₈.dmem (r.off 1592) (pbytesB r.sigB) := by
    have g0 := hA4.get (o := 1592) (n := 128) (bs := slice r.sigB 5268 128)
      (by simp [A4, A3, A2, A1, L3, L2p, L2, L1])
    have g1 := hA4.get (o := 1720) (n := 128) (bs := slice r.sigB 6424 128)
      (by simp [A4, A3, A2, A1, L3, L2p, L2])
    have g2 := hA4.get (o := 1848) (n := 160) (bs := slice r.sigB 7580 160)
      (by simp [A4, A3, A2, A1, L3, L2p])
    refine BytesAt.append g0 (BytesAt.append ?_ ?_)
    · rw [length_slice (by rw [r.hsig]; decide), off_add]; exact g1
    · rw [length_slice (by rw [r.hsig]; decide), length_slice (by rw [r.hsig]; decide), off_add,
        show (128#64 : BitVec 64) = BitVec.ofNat 64 128 from rfl, off_add]
      exact g2
  refine memcpy_block r hp hpre hc b33_in_code (jn := b34Offset) rfl run_b33 (by decide) rfl hF₈ ⟨hbp₈, trivial⟩
    trivial (a := 17004) (s := 1592) (n := 416) (by decide) (by decide) (by decide) fun m₉ hm₉ ↦
    ⟨regIs_ptr0 r rfl hm₉ rfl, regIs_ptr0 r rfl hm₉ rfl, rdx_lit hm₉ rfl (by decide),
      fun m₁₀ hF₁₀ hS₁₀ hB₁₀ hout₁₀ hc₉ ↦ .done _ ⟨rfl, hF₁₀, ?_,
        regIs_saved hS₁₀ rfl ((hm₉.regs .r13 _ rfl).trans h13₈),
        regIs_saved hS₁₀ rfl (hm₉.regs .rbp _ rfl)⟩⟩
  have hc2 : BytesAt m₉.dmem (r.off 20516) (slice r.sigB 6552 4).reverse :=
    bytesAt_low hm₉ (r := 0) (o := 20516) (sz := 21632)
      (v := .un .trunc .W32 (.reg .r15)) rfl (by decide) (by decide) h15₈.trunc
  have hL₉ := Facts.of_block r rfl hm₉ hA4 (by facts_dec4)
  have hp₉ := bytesAt_of_block r rfl hm₉ hpaths (N := 416) (by decide)
    (le_of_eq (length_pbytesB r.hsig)) (by decide)
  exact Facts.snoc2
    (Facts.of_call r hpre hc₉ (by decide) (Nat.zero_le _) hout₁₀ hL₉ (by facts_dec4))
    ⟨hl4 6552 (by decide), r.bytesAt_of_call hpre hc₉ (by decide) (Nat.zero_le _) hout₁₀
      (by rw [hl4 6552 (by decide)]; decide) (by right; decide) hc2⟩
    ⟨length_pbytesB r.hsig, by rwa [← length_pbytesB r.hsig, bytesOf_of_bytesAt hp₉] at hB₁₀⟩

end

end NativeRustcX64.SphincsVerifyProof.Parse
