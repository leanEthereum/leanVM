module

public import NativeRustcX64.WotsLeaf.Leaf.Hash

/-!
# The result written

From `b56` (directive 554) with the leaf's hash at `1048`: the 58 digits and the leaf's first 16
bytes copied to `112 .. 186` and `memcpy` of their 74 bytes to `out + 1` (`b56`), the tag 1 at
`out` (`b57`), the return (`finish`) (`leaf_out`). The result is the model's
(`result_some`).
-/

namespace NativeRustcX64.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcX64.Sym NativeRustcX64.Xmss.WotsLeaf Leaf
open LeanVM.Protocol.KeccakHash

@[expose] public section

/-- Each of the `n` bytes at `dst` of region 0 is the newest write of a load of region 0 of at most
8 bytes, of the byte at `src` with the same index. -/
def copyOK (ws : List Write) (dst src n : Nat) : Bool :=
  (List.range n).all fun j ↦ match findWrite 0 (dst + j) ws with
    | some (.load 0 s k, t) => decide (s + t = src + j) && decide (t < k) && decide (k ≤ 8)
    | _ => false

end

public section

/-- The result when the digest is a codeword. -/
theorem result_some (r : Run) (h : isCodeword r.dNum = true) :
    r.result = some (r.digitsPre 58, (Keccak.hashBytes r.leafIn).take 16) := by
  simp only [Run.result, wotsLeaf, messageDigest_eq, codeword, leNat_digest16, h, ite_true]
  rfl

section
variable [Labels] {r : Run}

/-- **Bytes copied in the frame** by loads of at most 8 bytes (`copyOK`). -/
theorem frame_copy {m m' : MachineData} {extra : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {S : SState} (hm : Match (r.envR m extra ret) S m') {dst src n : Nat} (hd : dst + n ≤ 2784)
    (hc : copyOK S.mem dst src n = true) {bs : List UInt8} (hl : bs.length = n)
    (h : BytesAt m.dmem (r.off src) bs) : BytesAt m'.dmem (r.off dst) bs := by
  intro j hj
  have hcj := List.all_eq_true.mp hc j (List.mem_range.mpr (by omega))
  rw [Run.off, addr_add_add, hm.mem 0 r.base 2784 rfl (dst + j) (by omega), memByte]
  split at hcj
  · rename_i s k t hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcj
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcj
    rw [hf]
    show some (byteOf ((r.envR m extra ret).load 0 s k) t) = _
    rw [byteOf_load h2 h3, h1, show (r.envR m extra ret).base 0 = r.base from rfl, ← addr_add_add]
    rw [show r.base + BitVec.ofNat 64 src = r.off src from rfl,
      show (r.envR m extra ret).mem0 = m.dmem from rfl, h j hj]
    rfl
  · cases hcj

omit [Labels] in
theorem byteOf_trunc_zext16 (y : BitVec 64) {t : Nat} (ht : t < 2) :
    byteOf (UnOp.apply .trunc .W16 (UnOp.apply (.zext .W16) .W32 y)) t = byteOf y t := by
  have h16 : Width.W16.bits = 16 := rfl
  have h32 : Width.W32.bits = 32 := rfl
  have hv : (UnOp.apply .trunc .W16 (UnOp.apply (.zext .W16) .W32 y)).toNat = y.toNat % 2 ^ 16 := by
    simp only [UnOp.apply, ext, Sym.low, BitVec.toNat_setWidth, h16, h32]
    omega
  apply UInt8.toNat_inj.mp
  rw [byteOf, byteOf, UInt8.toNat_ofNat', UInt8.toNat_ofNat', hv]
  obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
  all_goals simp only [Nat.mul_zero, Nat.mul_one, Nat.pow_zero, Nat.div_one]; omega

/-- **Two bytes copied** by a zero-extending 16-bit load. -/
theorem frame_copy2z {m m' : MachineData} {extra : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {S : SState} (hm : Match (r.envR m extra ret) S m') {o o' : Nat} (ho : o + 2 ≤ 2784)
    (hc : covers S.mem 0 o 2 (.un .trunc .W16 (.un (.zext .W16) .W32 (.load 0 o' 2))) = true)
    {bs : List UInt8} (hl : bs.length = 2) (h : BytesAt m.dmem (r.off o') bs) :
    BytesAt m'.dmem (r.off o) bs := by
  have hw := frame_covers hm ho hc
  intro j hj
  have := hw j (by simp; omega)
  rw [List.getElem_map, List.getElem_range] at this
  rw [this]
  show some (byteOf (UnOp.apply .trunc .W16 (UnOp.apply (.zext .W16) .W32
    ((r.envR m extra ret).load 0 o' 2))) j) = _
  rw [byteOf_trunc_zext16 _ (by omega), byteOf_load (by omega) (by decide),
    show (r.envR m extra ret).base 0 = r.base from rfl, ← addr_add_add,
    show r.base + BitVec.ofNat 64 o' = r.off o' from rfl,
    show (r.envR m extra ret).mem0 = m.dmem from rfl, h j hj]
  rfl

end

variable [Host] {r : Run}

theorem leaf_out (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre)
    (hcw : isCodeword r.dNum = true) {m : MachineData}
    (hK : Keep r (r.outerSlots 58 ++ [(1048, 32, Keccak.hashBytes r.leafIn)]) m) :
    Eventually (step1 Host.exe) r.Done ⟨m, r.pc NativeRustcX64.Xmss.WotsLeaf.b56Offset⟩ := by
  obtain ⟨-, -, -, s96, -, s614, -⟩ : SlotsAt r m r.chainSlots := allOf_left (allOf_left hK.2)
  obtain ⟨⟨-, -, hH⟩, -⟩ := allOf_right hK.2
  have hpo := r.pre_out hpre
  have hin : WotsLeafPre.Input r.m0 (r.out + BitVec.ofNat 64 1) 74 :=
    Run.Input.sub r hpo (by omega) (by omega)
  have hb := r.base_toNat hpre
  have hbl := r.below_toNat hpre
  have hc8 := r.callSp_toNat hpre
  have hon : r.out.toNat + 75 ≤ 2 ^ 64 := hpo.2.1
  have hoA : r.out.toNat + 75 ≤ (stackBelow r.m0 wotsLeafStack).toNat ∨
      (stackBelow r.m0 wotsLeafStack).toNat + 3464 ≤ r.out.toNat := hpo.2.2
  -- No byte of the frame is in `out`.
  have nout : ∀ o, o < 2768 → ¬InRange r.out 75 (r.off o) := fun o ho hin' ↦ by
    rw [Sym.inRange_iff hon, r.off_toNat hpre (by omega)] at hin'
    omega
  have out1 : ∀ p, InRange (r.out + BitVec.ofNat 64 1) 74 p → InRange r.out 75 p := fun p hp' ↦ by
    have e : (r.out + BitVec.ofNat 64 1).toNat = r.out.toNat + 1 := Sym.toNat_add_ofNat _ _ (by omega)
    rw [Sym.inRange_iff (by rw [e]; omega), e] at hp'
    rw [Sym.inRange_iff hon]
    omega
  -- `b56`: the digits and the leaf copied to `112`, `memcpy` to `out + 1`.
  refine frameCall r hp hpre b56_in_code (List.cons_ne_nil _ _) run_b56 (by decide) rfl hK
    trivial extraOK_nil trivial trivial trivial hc.1 fun m₁ hm₁ hK₁ _ ↦ ?_
  have d1 : BytesAt m₁.dmem (r.off 112) ((r.digitsPre 58).take 56) :=
    frame_copy hm₁ (dst := 112) (src := 614) (n := 56) (by decide) (by decide +kernel)
      (by simp [length_digitsPre]) (take_of_bytesAt s614.2.2 56)
  have d2 : BytesAt m₁.dmem (r.off 168) ((r.digitsPre 58).drop 56) := by
    have := BytesAt.sub s614.2.2 56 2
    rw [List.take_of_length_le (by simp [length_digitsPre])] at this
    exact frame_copy2z hm₁ (o := 168) (o' := 670) (by decide) (by decide +kernel)
      (by simp [length_digitsPre]) this
  have d3 : BytesAt m₁.dmem (r.off 170) ((Keccak.hashBytes r.leafIn).take 16) :=
    frame_copy hm₁ (dst := 170) (src := 1048) (n := 16) (by decide) (by decide +kernel)
      (by simp [length_hashBytes]) (take_of_bytesAt hH 16)
  have hX : BytesAt m₁.dmem (r.off 112)
      (r.digitsPre 58 ++ (Keccak.hashBytes r.leafIn).take 16) := by
    refine BytesAt.cat ?_ d3 (by simp [length_digitsPre])
    rw [← List.take_append_drop 56 (r.digitsPre 58)]
    exact BytesAt.cat d1 d2 (by simp [length_digitsPre])
  have hXl : (r.digitsPre 58 ++ (Keccak.hashBytes r.leafIn).take 16).length = 74 := by
    simp [length_digitsPre, length_hashBytes]
  have hbx₁ : Run.RegIs m₁ .rbx r.out := regIs_eval hm₁ (v := .load 0 96 8) rfl (r.load_word s96.2.2)
  have hdi₁ : Run.RegIs m₁ .rdi (r.out + BitVec.ofNat 64 1) := by
    refine regIs_eval hm₁ (v := .bin .add .W64 (.load 0 96 8) (.lit 1)) rfl ?_
    show BinOp.apply .add .W64 ((r.envR m [] _).load 0 96 8) (BitVec.ofNat 64 1) = _
    rw [r.load_word s96.2.2]
    simp only [BinOp.apply, low_W64, ext_W64]
  have hsi₁ : Run.RegIs m₁ .rsi (r.off 112) := regIs_ptr hm₁ rfl
  have hdx₁ := toNat_of_lit hm₁ (y := .rdx) (c := 74) rfl (by decide)
  have hF₁ := hK₁.1
  have hsp₁ : rspOf m₁ = r.base - 8#64 := hF₁.1
  refine ⟨?_, fun m₂ hsp₂ hQ₂ ↦ ?_⟩
  · simp only [MemcpyPre]
    rw [hdx₁, show reg m₁ .rdi = r.out + BitVec.ofNat 64 1 from hdi₁,
      show reg m₁ .rsi = r.off 112 from hsi₁]
    obtain ⟨ms, ws⟩ := r.frame_mapped hpre hF₁ (a := 112) (n := 74) (by decide)
    have o112 := r.off_toNat hpre (a := 112) (by decide)
    have hd : (r.out + BitVec.ofNat 64 1).toNat + 74 ≤ (stackBelow r.m0 wotsLeafStack).toNat ∨
        (stackBelow r.m0 wotsLeafStack).toNat + 3464 ≤ (r.out + BitVec.ofNat 64 1).toNat :=
      hin.2.2
    have hdw : (r.out + BitVec.ofNat 64 1).toNat + 74 ≤ 2 ^ 64 := hin.2.1
    refine ⟨r.stackOk hpre hF₁ (by decide), fun i hi ↦ hF₁.kept _ (hin.1 i hi), ms, hin.2.1, ws,
      ?_, ?_⟩
    · unfold Apart
      omega
    · unfold Apart
      rw [hsp₁]
      omega
  simp only [MemcpyPost] at hQ₂
  rw [hdx₁, show reg m₁ .rdi = r.out + BitVec.ofNat 64 1 from hdi₁,
    show reg m₁ .rsi = r.off 112 from hsi₁] at hQ₂
  obtain ⟨-, hB₂, hout₂, hS₂⟩ := hQ₂
  rw [← hXl, bytesOf_of_bytesAt hX] at hB₂
  have in1 : ∀ p, InRange r.out 1 p → InRange r.out 75 p := fun p hp' ↦ by
    rw [Sym.inRange_iff (by omega)] at hp'
    rw [Sym.inRange_iff hon]
    omega
  have nout1 : ∀ o, o < 2768 → ¬InRange (r.out + BitVec.ofNat 64 1) 74 (r.off o) :=
    fun o ho h ↦ nout o ho (out1 _ h)
  -- After `memcpy`: RSP the base, the entry's mapped bytes kept.
  have hrsp₂ : reg m₂ .rsp = r.base := by
    show rspOf m₂ = r.base
    rw [hsp₂, hsp₁, r.callSp_add]
  have hk₂ : Kept r.m0.dmem m₂.dmem := fun p h ↦ hS₂.2 p (hF₁.kept p h)
  have hs₂ : SameOutside r.m0.dmem m₂.dmem r.Changed := fun p hp =>
    (hout₂ p (fun h => hp (Or.inl (out1 p h)))).trans
      (hF₁.2.2.1 p (fun h => hp (Or.inr h)))
  have h96₂ : BytesAt m₂.dmem (r.off 96) (regBytes r.out) :=
    bytesAt_of_sameOutside (allOf_left (allOf_left hK₁.2)).2.2.2.1.2.2 hout₂ fun i hi ↦ by
      rw [Run.off_add]
      exact nout1 _ (by rw [length_regBytes] at hi; omega)
  have hsv₂ : BytesAt m₂.dmem (r.off 2712) (savedBytes r.m0) :=
    bytesAt_of_sameOutside hF₁.2.1 hout₂ fun i hi ↦ by
      rw [Run.off_add]
      exact nout1 _ (by rw [Run.length_savedBytes] at hi; omega)
  -- `b57`: the tag 1 at `out`.
  have hwf := envR_wf hpre hk₂ (r.extraOK_input hpre hk₂ hpo
    (fun l hl => ((r.got hpre).1 l hl).2.2.2 (r.out, 75) (by simp)))
    (r.pc (NativeRustcX64.Xmss.WotsLeaf.b57Offset + b57.length)).toBitVec
  have hm₂ : Match (r.envR m₂ [(r.out, 75)] (r.pc (NativeRustcX64.Xmss.WotsLeaf.b57Offset + b57.length)).toBitVec)
      (outS [(.rbx, .ptr 4 0)]) m₂ := by
    refine match_frameS (fun _ hl _ hi => r.got_byte_changed hpre hs₂ hl hi)
      hrsp₂ (sextra := [75]) (extra := [(r.out, 75)])
      (ret := (r.pc (NativeRustcX64.Xmss.WotsLeaf.b57Offset + b57.length)).toBitVec) (k := [(.rbx, .ptr 4 0)]) (bounds := [])
      (aliases := [(.load 0 96 8, (4, 0))]) ⟨rfl, trivial⟩ ⟨?_, trivial⟩ trivial ⟨?_, trivial⟩
    · show m₂.regs.get64 .rbx = r.out + BitVec.ofInt 64 0
      rw [hS₂.1 .rbx rfl, show m₁.regs.get64 .rbx = r.out from hbx₁]
      simp
    · show (r.envR m₂ [(r.out, 75)] _).load 0 96 8 = r.out + BitVec.ofInt 64 0
      rw [r.load_word h96₂]
      simp
  refine blk r hp b57_in_code (List.cons_ne_nil _ _) run_b57 hwf rfl hm₂ fun st hm₃ hpc₃ ↦ ?_
  have hso : SameOutside m₂.dmem st.data.dmem (InRange r.out 1) := by
    refine SameOutside.mono (hm₃.sameOutside hwf) fun p ⟨w, hw, b, sz, hbw, h1, h2⟩ ↦ ?_
    obtain rfl := List.mem_singleton.mp hw
    cases hbw
    rw [Sym.inRange_iff (by omega)]
    dsimp only at h1 h2
    omega
  have hT : BytesAt st.data.dmem (r.out + BitVec.ofNat 64 0) [1] := by
    have := bytesAt_write_val hm₃ (r := 4) (o := 0) (n := 1) (b := r.out) (sz := 75) rfl
      (by decide) (v := .lit 1) (by decide +kernel)
    rwa [show (Sym.lit 1).eval (r.envR m₂ [(r.out, 75)] (r.pc (NativeRustcX64.Xmss.WotsLeaf.b57Offset + b57.length)).toBitVec) =
      BitVec.ofNat 64 1 from rfl, bytes_byte] at this
  have hX₃ : BytesAt st.data.dmem (r.out + BitVec.ofNat 64 1)
      (r.digitsPre 58 ++ (Keccak.hashBytes r.leafIn).take 16) :=
    bytesAt_of_sameOutside hB₂ hso fun i hi h ↦ by
      rw [hXl] at hi
      have e : (r.out + BitVec.ofNat 64 1 + BitVec.ofNat 64 i).toNat = r.out.toNat + 1 + i := by
        rw [addr_add_add, Sym.toNat_add_ofNat _ _ (by omega)]
        omega
      rw [Sym.inRange_iff (by omega), e] at h
      omega
  have hall : BytesAt st.data.dmem r.out
      (1 :: (r.digitsPre 58 ++ (Keccak.hashBytes r.leafIn).take 16)) :=
    BytesAt.append (bs := [1]) (BytesAt.zero hT) hX₃
  have hbytes : bytesOf st.data.dmem r.out 75 =
      1 :: (r.digitsPre 58 ++ (Keccak.hashBytes r.leafIn).take 16) := by
    have := bytesOf_of_bytesAt hall
    rwa [List.length_cons, hXl] at this
  refine pc_at (hpc₃.trans (Run.label_of_block r hp b12_in_code rfl)) ?_
  refine finish r hp hpre st.data ?_ ?_ (fun p h ↦ hm₃.kept hwf p (hk₂ p h)) ?_ ?_
  · unfold reg
    rw [hm₃.regs .rsp _ rfl, show (0 : Int) = ((0 : Nat) : Int) from rfl, eval_ptr0, Run.off_zero]
  · exact bytesAt_of_sameOutside hsv₂ hso fun i hi h ↦ by
      rw [Run.off_add] at h
      exact nout _ (by rw [Run.length_savedBytes] at hi; omega) (in1 _ h)
  · intro p hp'
    rw [hso p fun h ↦ hp' (.inl (in1 p h)), hout₂ p fun h ↦ hp' (.inl (out1 p h)),
      hF₁.2.2.1 p fun h ↦ hp' (.inr h)]
  · rw [result_some r hcw, hbytes]
    show List.take 75 _ = _
    rw [List.take_of_length_le (by simp [length_digitsPre, length_hashBytes])]

end

end NativeRustcX64.WotsLeafProof
