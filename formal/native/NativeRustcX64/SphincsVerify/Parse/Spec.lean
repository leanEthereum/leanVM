module

public import NativeRustcX64.SphincsVerify.Parse.Assemble

/-!
# The parse (x86-64): `parse_spec : ParseSpec`

From the entry: the prologue (`prologue_spec`), the raw signature (`words_spec`), the key and the
openings (`b9_spec`, `open_loop`), the three layers (`layer0_spec`, `layer1_spec`,
`layer2_spec`), the assembly (`assemble_spec`); at `b43` the facts give `AtHMsg`: the key at
`112`, the parsed signature at `20556` (`ParseMem.sigMem_eq`), RBP the randomizer, the message at
`2008`, the first layer's address at `184`.
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustc.Sphincs.ParseMem NativeRustcX64.Sym
  NativeRustcX64.Sphincs.SphincsVerify LeanVM.Protocol.KeccakHash

public section

theorem le32_eq (x : UInt32) : le32 x = (be32 x).reverse := rfl

/-- **The facts at `b43`** are `AtHMsg`'s. -/
theorem atHMsg_of (r : Run) [Labels] {m : MachineData} (hF : r.Frame m) (hL : Facts r m.dmem (A5 r))
    (hbp : Run.RegIs m .r15 (r.off 25196))
    (h12 : Run.RegIs m .rbp (Labels.label "memcpy").toBitVec) : r.AtHMsg m := by
  have g : ∀ {o n : Nat} {bs : List UInt8}, (o, n, bs) ∈ A5 r → BytesAt m.dmem (r.off o) bs :=
    fun h ↦ hL.get h
  have hsig : BytesAt m.dmem (r.off 20556) (sigMem r.sig) := by
    show BytesAt m.dmem (r.off 20556) (sigMem (sigOf r.w))
    rw [sigMem_eq]
    have e0 := g (o := 20556) (n := 4224) (bs := opens r) (by simp [A5, A4, A3, A2, A1])
    have e1 := g (o := 24780) (n := 416) (bs := pbytes r.w) (by simp [A5])
    have e2 := g (o := 25196) (n := 16) (bs := slice (sigBytes r.w) 0 16) (by simp [A5, A4, A3, A2, A1])
    have e3 := g (o := 25212) (n := 1024) (bs := slice (sigBytes r.w) 4244 1024)
      (by simp [A5, A4, A3, A2])
    have e4 := g (o := 26236) (n := 4) (bs := (be32 (r.w 538).toUInt32).reverse)
      (by simp [A5, A4, A3])
    have e5 := g (o := 26240) (n := 1024) (bs := slice (sigBytes r.w) 5400 1024) (by simp [A5, A4, A3])
    have e6 := g (o := 27264) (n := 4) (bs := (be32 (r.w 683).toUInt32).reverse) (by simp [A5, A4])
    have e7 := g (o := 27268) (n := 1024) (bs := slice (sigBytes r.w) 6556 1024) (by simp [A5, A4])
    have e8 := g (o := 28292) (n := 4) (bs := (be32 (r.w 828).toUInt32).reverse) (by simp [A5])
    have l0 : ((List.range 24).map (obytes r.w)).flatten.length = 4224 := length_opens r
    have ls : ∀ a n, a + n ≤ 7740 → (slice (sigBytes r.w) a n).length = n :=
      fun _ _ h ↦ length_slice_sig r.w h
    refine bytesAt_cat e0 l0 rfl (bytesAt_cat e1 (length_pbytes r.w) rfl
      (bytesAt_cat e2 (ls 0 16 (by decide)) rfl ?_))
    simp only [lbytes, le32_eq, List.append_assoc, show layerWordOff 0 = 538 from rfl,
      show layerWordOff 1 = 683 from rfl, show layerWordOff 2 = 828 from rfl, sigLayerOff]
    refine bytesAt_cat e3 (ls _ _ (by decide)) rfl (bytesAt_cat e4 (length_be32r _) rfl
      (bytesAt_cat e5 (ls _ _ (by decide)) rfl (bytesAt_cat e6 (length_be32r _) rfl
        (bytesAt_cat e7 (ls _ _ (by decide)) rfl ?_))))
    simpa using e8
  exact ⟨hF, ⟨g (o := 112) (n := 32) (by simp [A5, A4, A3, A2, A1, L3, L2, L1, L0, base3]), hsig⟩,
    hbp, g (o := 2008) (n := 32) (by simp [A5, A4, A3, A2, A1, L3, L2, L1, L0, base3]),
    g (o := 184) (n := 8) (by simp [A5, A4, A3, A2]), h12⟩

/-- **The parse** (`b0 .. b42`): from the entry, `AtHMsg` at `b43`. -/
theorem parse_spec [Host] : ParseSpec := by
  intro r hp hc hpre m hm
  subst hm
  refine Eventually.bind (prologue_spec r hp hc hpre) fun ⟨m, pc⟩ ⟨hpc, h⟩ ↦ ?_
  simp only at hpc
  subst hpc
  refine Eventually.bind (words_spec r hp hpre h) fun ⟨m, pc⟩ ⟨hpc, h⟩ ↦ ?_
  simp only at hpc
  subst hpc
  refine Eventually.bind (b9_spec r hp hpre h) fun ⟨m, pc⟩ ⟨hpc, h⟩ ↦ ?_
  simp only at hpc
  subst hpc
  refine Eventually.bind (open_loop r hp hpre hc h) fun ⟨m, pc⟩ ⟨hpc, h⟩ ↦ ?_
  simp only at hpc
  subst hpc
  refine Eventually.bind (layer0_spec r hp hpre hc h) fun ⟨m, pc⟩ ⟨hpc, h⟩ ↦ ?_
  simp only at hpc
  subst hpc
  refine Eventually.bind (layer1_spec r hp hpre hc h) fun ⟨m, pc⟩ ⟨hpc, h⟩ ↦ ?_
  simp only at hpc
  subst hpc
  refine Eventually.bind (layer2_spec r hp hpre hc h) fun ⟨m, pc⟩ ⟨hpc, h⟩ ↦ ?_
  simp only at hpc
  subst hpc
  exact Eventually.mono (assemble_spec r hp hpre hc h) fun st ⟨hpc, hF, hL, hbp, h12⟩ ↦
    ⟨hpc, atHMsg_of r hF hL hbp h12⟩

end

end NativeRustcX64.SphincsVerifyProof.Parse
