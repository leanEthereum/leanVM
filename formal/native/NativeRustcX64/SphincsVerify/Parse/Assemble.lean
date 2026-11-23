module

public import NativeRustcX64.SphincsVerify.Parse.Layer2

/-!
# The parse, part 9: the parsed signature assembled (`b38 .. b42`, x86-64)

`b38` copies the randomizer to `25180` (RBP its address) and `memcpy`s the openings to `20540`;
`b39` stores the first layer's address at `176` and `memcpy`s its chain values to `25196`;
`b40`, `b41` store the first two counters and `memcpy` the second and third layers' chain values;
`b42` stores the third counter and `memcpy`s the paths to `24764`. At `b43` (directive 451):
`AtHMsg` (`assemble_spec`), the parsed signature `sigMem r.sig` at `20540` (`sigMem_eq`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustc.Sphincs.ParseMem NativeRustcX64.Sym
  NativeRustcX64.Sphincs.SphincsVerify LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The `n` bytes at `o` of region `r` are the low bytes of `v`. -/
def holdsVal (ws : List Write) (r o n : Nat) (v : Sym) : Bool :=
  (List.range n).all fun i => findWrite r (o + i) ws == some (v, i)

/-- After `b38`: the randomizer, the openings. -/
def A1 (r : Run) : List (Nat × Nat × List UInt8) :=
  L3 r ++ [(25180, 16, slice (sigBytes r.w) 0 16), (20540, 4224, opens r)]

/-- After `b39`: the first layer's address, its chain values. -/
def A2 (r : Run) : List (Nat × Nat × List UInt8) :=
  A1 r ++ [(176, 8, wordBytes (r.addr 25196)), (25196, 1024, slice (sigBytes r.w) 4244 1024)]

/-- After `b40`: the first counter, the second layer's chain values. -/
def A3 (r : Run) : List (Nat × Nat × List UInt8) :=
  A2 r ++ [(26220, 4, (be32 (r.w 538).toUInt32).reverse),
    (26224, 1024, slice (sigBytes r.w) 5400 1024)]

/-- After `b41`: the second counter, the third layer's chain values. -/
def A4 (r : Run) : List (Nat × Nat × List UInt8) :=
  A3 r ++ [(27248, 4, (be32 (r.w 683).toUInt32).reverse),
    (27252, 1024, slice (sigBytes r.w) 6556 1024)]

/-- After `b42`: the third counter, the paths. -/
def A5 (r : Run) : List (Nat × Nat × List UInt8) :=
  A4 r ++ [(28276, 4, (be32 (r.w 828).toUInt32).reverse), (24764, 416, pbytes r.w)]

end

public section

/-- Decides the assembly's facts' checks. -/
macro "facts_dec4" : tactic => `(tactic| (
  simp only [A5, A4, A3, A2, A1, L3, L2, L1, L0, base3, List.cons_append, List.nil_append,
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

theorem length_opens (r : Run) : (opens r).length = 4224 := length_openings r.w le_rfl

theorem length_be32r (x : UInt32) : (be32 x).reverse.length = 4 := by simp [be32]

/-- Facts extended by two. -/
theorem Facts.snoc2 {r : Run} {d : DataMem} {L : List (Nat × Nat × List UInt8)} (h : Facts r d L)
    {o n o' n' : Nat} {bs bs' : List UInt8} (h1 : bs.length = n ∧ BytesAt d (r.off o) bs)
    (h2 : bs'.length = n' ∧ BytesAt d (r.off o') bs') :
    Facts r d (L ++ [(o, n, bs), (o', n', bs')]) := by
  rw [facts_append]
  exact ⟨h, h1, h2, trivial⟩

theorem mem_A1 (r : Run) : (4096, 4224, opens r) ∈ L3 r := by simp [L3, L2, L1, L0]

theorem raw_mem3 (r : Run) : (12416, 7740, sigBytes r.w) ∈ L3 r := by simp [L3, L2, L1, L0, base3]

variable (r : Run) [Host]

/-- **`b38 .. b42`**: the parsed signature assembled. -/
theorem assemble_spec (hp : Placed code r.k) (hpre : r.Pre) (hc : Callees) {m : MachineData}
    (h : LS3 r m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b43Offset ∧ r.Frame st.data ∧
      Facts r st.data.dmem (A5 r) ∧ Run.RegIs st.data .rbp (r.off 25180) ∧
      Run.RegIs st.data .r12 (Labels.label "memcpy").toBitVec) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b38Offset⟩ := by
  obtain ⟨hF, hL, hbx, h15, h14, h13, h12⟩ := h
  -- `b38`: the randomizer, the openings
  refine memcpy_block r hp hpre hc b38_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b39Offset) rfl run_b38 (by decide) rfl hF ⟨h12, trivial⟩
    trivial (a := 20540) (s := 4096) (n := 4224) (by decide) (by decide) (by decide) fun m₁ hm₁ ↦
    ⟨regIs_ptr0 r hm₁ rfl, regIs_ptr0 r hm₁ rfl, rdx_lit hm₁ rfl (by decide),
      fun m₂ hF₂ hS hB hout hc₁ ↦ ?_⟩
  have hrand : BytesAt m₁.dmem (r.off 25180) (slice (sigBytes r.w) 0 16) :=
    copy hm₁ (r := 0) (o := 25180) (r' := 0) (o' := 12416) (n := 16) rfl (by decide) (by decide)
      (length_slice_sig r.w (by decide)) (raw_slice r (hL.get (raw_mem3 r)) (k := 0) (n := 16)
        (by decide))
  have hL₁ := Facts.of_block r rfl hm₁ hL (by facts_dec4)
  have ho₁ := bytesAt_of_block r rfl hm₁ (hL.get (mem_A1 r)) (N := 4224) (by decide)
    (le_of_eq (length_opens r)) (by decide)
  have hA1 : Facts r m₂.dmem (A1 r) := Facts.snoc2
    (Facts.of_call r hpre hc₁ (by decide) (Nat.zero_le _) hout hL₁ (by facts_dec4))
    ⟨length_slice_sig r.w (by decide), r.bytesAt_of_call hpre hc₁ (by decide) (Nat.zero_le _) hout
      (by rw [length_slice_sig r.w (by decide)]; decide)
      (by right; decide) hrand⟩
    ⟨length_opens r, by rwa [← length_opens r, bytesOf_of_bytesAt ho₁] at hB⟩
  have hbp₂ := regIs_saved hS rfl (regIs_ptr0 r hm₁ (y := .rbp) rfl)
  have h15₂ := low4_saved hS rfl (h15.of_eq (hm₁.regs .r15 _ rfl))
  have h14₂ := low4_saved hS rfl (h14.of_eq (hm₁.regs .r14 _ rfl))
  have h13₂ := low4_saved hS rfl (h13.of_eq (hm₁.regs .r13 _ rfl))
  have hbx₂ := regIs_saved hS rfl ((hm₁.regs .rbx _ rfl).trans hbx)
  have h12₂ := regIs_saved hS rfl (hm₁.regs .r12 _ rfl : Run.RegIs m₁ .r12 (Labels.label "memcpy").toBitVec)
  -- `b39`: the first layer's address, its chain values
  refine memcpy_block r hp hpre hc b39_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b40Offset) rfl run_b39 (by decide) rfl hF₂ ⟨h12₂, trivial⟩
    trivial (a := 25196) (s := 8320) (n := 1024) (by decide) (by decide) (by decide) fun m₃ hm₃ ↦
    ⟨regIs_ptr0 r hm₃ rfl, regIs_ptr0 r hm₃ rfl, rdx_lit hm₃ rfl (by decide),
      fun m₄ hF₄ hS₄ hB₄ hout₄ hc₃ ↦ ?_⟩
  have h176 : BytesAt m₃.dmem (r.off 176) (wordBytes (r.addr 25196)) := by
    have := bytesAt_val hm₃ (r := 0) (o := 176) (n := 8) (v := .ptr 0 25196) rfl (by decide)
      (by decide)
    have e : Sym.eval (r.env m₂ (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b40Offset).toBitVec) (.ptr 0 (25196 : Nat)) =
        r.off 25196 := eval_base r rfl 25196
    rw [show ((25196 : Nat) : Int) = 25196 from rfl] at e
    rw [e] at this
    have h2 : (List.range 8).map (byteOf (r.off 25196)) = wordBytes (r.addr 25196) :=
      regBytes_eq_wordBytes (r.off 25196)
    rw [h2] at this
    exact this
  have hL₃ := Facts.of_block r rfl hm₃ hA1 (by facts_dec4)
  have hcv₃ := bytesAt_of_block r rfl hm₃ (hA1.get (o := 8320) (n := 1024)
    (bs := slice (sigBytes r.w) 4244 1024) (by simp [A1, L3, L2, L1]))
    (N := 1024) (by decide) (le_of_eq (length_slice_sig r.w (by decide))) (by decide)
  have hA2 : Facts r m₄.dmem (A2 r) := Facts.snoc2
    (Facts.of_call r hpre hc₃ (by decide) (Nat.zero_le _) hout₄ hL₃ (by facts_dec4))
    ⟨length_wordBytes _, r.bytesAt_of_call hpre hc₃ (by decide) (Nat.zero_le _) hout₄
      (by rw [length_wordBytes]; decide) (by left; rw [length_wordBytes]; decide) h176⟩
    ⟨length_slice_sig r.w (by decide), by
      rwa [← length_slice_sig r.w (a := 4244) (n := 1024) (by decide), bytesOf_of_bytesAt hcv₃]
        at hB₄⟩
  have hbp₄ := regIs_saved hS₄ rfl ((hm₃.regs .rbp _ rfl).trans hbp₂)
  have h15₄ := low4_saved hS₄ rfl (h15₂.of_eq (hm₃.regs .r15 _ rfl))
  have h14₄ := low4_saved hS₄ rfl (h14₂.of_eq (hm₃.regs .r14 _ rfl))
  have h13₄ := low4_saved hS₄ rfl (h13₂.of_eq (hm₃.regs .r13 _ rfl))
  have hbx₄ := regIs_saved hS₄ rfl ((hm₃.regs .rbx _ rfl).trans hbx₂)
  have h12₄ := regIs_saved hS₄ rfl (hm₃.regs .r12 _ rfl : Run.RegIs m₃ .r12 (Labels.label "memcpy").toBitVec)
  -- `b40`: the first counter, the second layer's chain values
  refine memcpy_block r hp hpre hc b40_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b41Offset) rfl run_b40 (by decide) rfl hF₄ ⟨h12₄, trivial⟩
    trivial (a := 26224) (s := 10368) (n := 1024) (by decide) (by decide) (by decide) fun m₅ hm₅ ↦
    ⟨regIs_ptr0 r hm₅ rfl, regIs_ptr0 r hm₅ rfl, rdx_lit hm₅ rfl (by decide),
      fun m₆ hF₆ hS₆ hB₆ hout₆ hc₅ ↦ ?_⟩
  have hc0 : BytesAt m₅.dmem (r.off 26220) (be32 (r.w 538).toUInt32).reverse :=
    bytesAt_low hm₅ (r := 0) (o := 26220) (sz := 29392)
      (v := .un .trunc .W32 (.reg .r15)) rfl (by decide) (by decide) h15₄.trunc
  have hL₅ := Facts.of_block r rfl hm₅ hA2 (by facts_dec4)
  have hcv₅ := bytesAt_of_block r rfl hm₅ (hA2.get (o := 10368) (n := 1024)
    (bs := slice (sigBytes r.w) 5400 1024) (by simp [A2, A1, L3, L2]))
    (N := 1024) (by decide) (le_of_eq (length_slice_sig r.w (by decide))) (by decide)
  have hA3 : Facts r m₆.dmem (A3 r) := Facts.snoc2
    (Facts.of_call r hpre hc₅ (by decide) (Nat.zero_le _) hout₆ hL₅ (by facts_dec4))
    ⟨length_be32r _, r.bytesAt_of_call hpre hc₅ (by decide) (Nat.zero_le _) hout₆
      (by rw [length_be32r]; decide) (by left; rw [length_be32r]) hc0⟩
    ⟨length_slice_sig r.w (by decide), by
      rwa [← length_slice_sig r.w (a := 5400) (n := 1024) (by decide), bytesOf_of_bytesAt hcv₅]
        at hB₆⟩
  have hbp₆ := regIs_saved hS₆ rfl ((hm₅.regs .rbp _ rfl).trans hbp₄)
  have h14₆ := low4_saved hS₆ rfl (h14₄.of_eq (hm₅.regs .r14 _ rfl))
  have h13₆ := low4_saved hS₆ rfl (h13₄.of_eq (hm₅.regs .r13 _ rfl))
  have hbx₆ := regIs_saved hS₆ rfl ((hm₅.regs .rbx _ rfl).trans hbx₄)
  have h12₆ := regIs_saved hS₆ rfl (hm₅.regs .r12 _ rfl : Run.RegIs m₅ .r12 (Labels.label "memcpy").toBitVec)
  -- `b41`: the second counter, the third layer's chain values
  refine memcpy_block r hp hpre hc b41_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b42Offset) rfl run_b41 (by decide) rfl hF₆
    ⟨hbx₆.trans (eval_base r rfl 11392).symm, h12₆, trivial⟩ trivial (a := 27252) (s := 11392)
    (n := 1024) (by decide) (by decide) (by decide) fun m₇ hm₇ ↦
    ⟨regIs_ptr0 r hm₇ rfl, regIs_ptr0 r hm₇ rfl, rdx_lit hm₇ rfl (by decide),
      fun m₈ hF₈ hS₈ hB₈ hout₈ hc₇ ↦ ?_⟩
  have hc1 : BytesAt m₇.dmem (r.off 27248) (be32 (r.w 683).toUInt32).reverse :=
    bytesAt_low hm₇ (r := 0) (o := 27248) (sz := 29392)
      (v := .un .trunc .W32 (.reg .r14)) rfl (by decide) (by decide) h14₆.trunc
  have hL₇ := Facts.of_block r rfl hm₇ hA3 (by facts_dec4)
  have hcv₇ := bytesAt_of_block r rfl hm₇ (hA3.get (o := 11392) (n := 1024)
    (bs := slice (sigBytes r.w) 6556 1024) (by simp [A3, A2, A1, L3]))
    (N := 1024) (by decide) (le_of_eq (length_slice_sig r.w (by decide))) (by decide)
  have hA4 : Facts r m₈.dmem (A4 r) := Facts.snoc2
    (Facts.of_call r hpre hc₇ (by decide) (Nat.zero_le _) hout₈ hL₇ (by facts_dec4))
    ⟨length_be32r _, r.bytesAt_of_call hpre hc₇ (by decide) (Nat.zero_le _) hout₈
      (by rw [length_be32r]; decide) (by left; rw [length_be32r]) hc1⟩
    ⟨length_slice_sig r.w (by decide), by
      rwa [← length_slice_sig r.w (a := 6556) (n := 1024) (by decide), bytesOf_of_bytesAt hcv₇]
        at hB₈⟩
  have hbp₈ := regIs_saved hS₈ rfl ((hm₇.regs .rbp _ rfl).trans hbp₆)
  have h13₈ := low4_saved hS₈ rfl (h13₆.of_eq (hm₇.regs .r13 _ rfl))
  have h12₈ := regIs_saved hS₈ rfl (hm₇.regs .r12 _ rfl : Run.RegIs m₇ .r12 (Labels.label "memcpy").toBitVec)
  -- `b42`: the third counter, the paths
  have hpaths : BytesAt m₈.dmem (r.off 1632) (pbytes r.w) := by
    have g0 := hA4.get (o := 1632) (n := 128) (bs := slice (sigBytes r.w) 5268 128)
      (by simp [A4, A3, A2, A1, L3, L2, L1])
    have g1 := hA4.get (o := 1760) (n := 128) (bs := slice (sigBytes r.w) 6424 128)
      (by simp [A4, A3, A2, A1, L3, L2])
    have g2 := hA4.get (o := 1888) (n := 160) (bs := slice (sigBytes r.w) 7580 160)
      (by simp [A4, A3, A2, A1, L3])
    refine BytesAt.append g0 (BytesAt.append ?_ ?_)
    · rw [length_slice_sig r.w (by decide), off_add]; exact g1
    · rw [length_slice_sig r.w (by decide), length_slice_sig r.w (by decide), off_add,
        show (128#64 : BitVec 64) = BitVec.ofNat 64 128 from rfl, off_add]
      exact g2
  refine memcpy_block r hp hpre hc b42_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b43Offset) rfl run_b42 (by decide) rfl hF₈ ⟨h12₈, trivial⟩
    trivial (a := 24764) (s := 1632) (n := 416) (by decide) (by decide) (by decide) fun m₉ hm₉ ↦
    ⟨regIs_ptr0 r hm₉ rfl, regIs_ptr0 r hm₉ rfl, rdx_lit hm₉ rfl (by decide),
      fun m₁₀ hF₁₀ hS₁₀ hB₁₀ hout₁₀ hc₉ ↦ .done _ ⟨rfl, hF₁₀, ?_,
        regIs_saved hS₁₀ rfl ((hm₉.regs .rbp _ rfl).trans hbp₈),
        regIs_saved hS₁₀ rfl (hm₉.regs .r12 _ rfl)⟩⟩
  have hc2 : BytesAt m₉.dmem (r.off 28276) (be32 (r.w 828).toUInt32).reverse :=
    bytesAt_low hm₉ (r := 0) (o := 28276) (sz := 29392)
      (v := .un .trunc .W32 (.reg .r13)) rfl (by decide) (by decide) h13₈.trunc
  have hL₉ := Facts.of_block r rfl hm₉ hA4 (by facts_dec4)
  have hp₉ := bytesAt_of_block r rfl hm₉ hpaths (N := 416) (by decide)
    (le_of_eq (length_pbytes r.w)) (by decide)
  exact Facts.snoc2
    (Facts.of_call r hpre hc₉ (by decide) (Nat.zero_le _) hout₁₀ hL₉ (by facts_dec4))
    ⟨length_be32r _, r.bytesAt_of_call hpre hc₉ (by decide) (Nat.zero_le _) hout₁₀
      (by rw [length_be32r]; decide) (by right; decide) hc2⟩
    ⟨length_pbytes r.w, by rwa [← length_pbytes r.w, bytesOf_of_bytesAt hp₉] at hB₁₀⟩

end

end NativeRustcX64.SphincsVerifyProof.Parse
