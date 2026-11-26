module

public import NativeRustcX64.SphincsVerify.Parse.Assemble

/-!
# The parse (x86-64): `parse_spec : ParseSpec`

From the entry: the prologue (`prologue_spec`), the 24 FORS openings (`open_loop`), the three
layers (`layer0_spec`, `layer1_spec`, `layer2_spec`), and the assembly (`assemble_spec`); at `b34`
the facts give `AtHMsg`: the key at `112`, the parsed signature at `12780`
(`ParseMem.sigMem_eq_bytes`), R13 the randomizer (`17420`), `msgPtr` at `8`, layer 0's chain
values' address at `184`, and RBP `memcpy`.
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustc.Sphincs.ParseMem NativeRustcX64.Sym
  NativeRustcX64.Sphincs.SphincsVerify LeanVM.Protocol.KeccakHash

public section

/-- **The facts at `b34`** are `AtHMsg`'s. -/
theorem atHMsg_of (r : Run) [Labels] {m : MachineData} (hF : r.Frame m) (hL : Facts r m.dmem (A5 r))
    (h13 : Run.RegIs m .r13 (r.off 17420))
    (hbp : Run.RegIs m .rbp (Labels.label "memcpy").toBitVec) : r.AtHMsg m := by
  have g : ∀ {o n : Nat} {bs : List UInt8}, (o, n, bs) ∈ A5 r → BytesAt m.dmem (r.off o) bs :=
    fun h ↦ hL.get h
  have hsig : BytesAt m.dmem (r.off 12780) (sigMem r.sig) := by
    show BytesAt m.dmem (r.off 12780) (sigMem (sigOfBytes r.sigB))
    rw [sigMem_eq_bytes r.hsig]
    have e0 := g (o := 12780) (n := 4224) (bs := opens r) (by simp [A5, A4, A3, A2, A1])
    have e1 := g (o := 17004) (n := 416) (bs := pbytesB r.sigB) (by simp [A5])
    have e2 := g (o := 17420) (n := 16) (bs := slice r.sigB 0 16) (by simp [A5, A4, A3, A2, A1])
    have e3 := g (o := 17436) (n := 1024) (bs := slice r.sigB 4244 1024) (by simp [A5, A4, A3, A2])
    have e4 := g (o := 18460) (n := 4) (bs := (slice r.sigB 4240 4).reverse) (by simp [A5, A4, A3])
    have e5 := g (o := 18464) (n := 1024) (bs := slice r.sigB 5400 1024) (by simp [A5, A4, A3])
    have e6 := g (o := 19488) (n := 4) (bs := (slice r.sigB 5396 4).reverse) (by simp [A5, A4])
    have e7 := g (o := 19492) (n := 1024) (bs := slice r.sigB 6556 1024) (by simp [A5, A4])
    have e8 := g (o := 20516) (n := 4) (bs := (slice r.sigB 6552 4).reverse) (by simp [A5])
    have l0 : ((List.range 24).map (obytesB r.sigB)).flatten.length = 4224 := length_opens r
    have ls : ∀ a n, a + n ≤ 7740 → (slice r.sigB a n).length = n :=
      fun _ _ h ↦ length_slice (by rw [r.hsig]; exact h)
    have lr : ∀ a, a + 4 ≤ 7740 → (slice r.sigB a 4).reverse.length = 4 :=
      fun a h ↦ by rw [List.length_reverse, ls a 4 h]
    refine bytesAt_cat e0 l0 rfl (bytesAt_cat e1 (length_pbytesB r.hsig) rfl
      (bytesAt_cat e2 (ls 0 16 (by decide)) rfl ?_))
    simp only [lbytesB, List.append_assoc, sigLayerOff]
    refine bytesAt_cat e3 (ls _ _ (by decide)) rfl (bytesAt_cat e4 (lr _ (by decide)) rfl
      (bytesAt_cat e5 (ls _ _ (by decide)) rfl (bytesAt_cat e6 (lr _ (by decide)) rfl
        (bytesAt_cat e7 (ls _ _ (by decide)) rfl ?_))))
    simpa using e8
  exact ⟨hF, ⟨g (o := 112) (n := 32) (by simp [A5, A4, A3, A2, A1, L3, L2p, L2, L1, L0c, L0, base3]), hsig⟩,
    h13, g (o := 8) (n := 8) (by simp [A5, A4, A3, A2, A1, L3, L2p, L2, L1, L0c, L0, base3]),
    g (o := 184) (n := 8) (by simp [A5, A4, A3, A2]), hbp⟩

/-- **The parse** (`b0 .. b33`): from the entry, `AtHMsg` at `b34`. -/
theorem parse_spec [Host] : ParseSpec := by
  intro r hp hc hpre m hm
  subst hm
  refine Eventually.bind (prologue_spec r hp hpre) fun ⟨m, pc⟩ ⟨hpc, h⟩ ↦ ?_
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
  exact Eventually.mono (assemble_spec r hp hpre hc h) fun st ⟨hpc, hF, hL, h13, hbp⟩ ↦
    ⟨hpc, atHMsg_of r hF hL h13 hbp⟩

end

end NativeRustcX64.SphincsVerifyProof.Parse
