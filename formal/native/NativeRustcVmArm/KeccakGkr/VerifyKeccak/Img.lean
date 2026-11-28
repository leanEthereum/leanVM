module

public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Copy

/-!
# Byte images: a range copied to another

`Img d p d' q n`: every byte of the `n` from `p` in `d` is at the same offset from `q` in `d'`.
Copies compose (`Img.trans`), split (`Img.append`, `Img.sub`), keep representations
(`Img.bytesAt`); a claim but its bit weights moves along (`ClaimAt.img`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeVm.Model
open NativeRustcVm.KeccakGkr (ClaimAt)

@[expose] public section

/-- The `n` bytes from `p` in `d` are at `q` in `d'`. -/
def Img (d : Mem 64) (p : BitVec 64) (d' : Mem 64) (q : BitVec 64) (n : Nat) : Prop :=
  ∀ j < n, ∀ b, d.get? (p + BitVec.ofNat 64 j) = some b → d'.get? (q + BitVec.ofNat 64 j) = some b

end

public section

variable {d d' d'' : Mem 64} {p q r : BitVec 64} {n : Nat}

theorem Img.trans (h : Img d p d' q n) (h' : Img d' q d'' r n) : Img d p d'' r n :=
  fun j hj b hb ↦ h' j hj b (h j hj b hb)

theorem Img.sub (h : Img d p d' q n) {o k : Nat} (hk : o + k ≤ n) :
    Img d (p + BitVec.ofNat 64 o) d' (q + BitVec.ofNat 64 o) k := fun j hj b hb ↦ by
  rw [NativeRustcVm.addr_add_add] at hb ⊢; exact h _ (by omega) b hb

theorem Img.append {n1 n2 : Nat} (h1 : Img d p d' q n1)
    (h2 : Img d (p + BitVec.ofNat 64 n1) d' (q + BitVec.ofNat 64 n1) n2) :
    Img d p d' q (n1 + n2) := fun j hj b hb ↦ by
  by_cases hj1 : j < n1
  · exact h1 j hj1 b hb
  · have := h2 (j - n1) (by omega) b
      (by rw [NativeRustcVm.addr_add_add, show n1 + (j - n1) = j by omega]; exact hb)
    rwa [NativeRustcVm.addr_add_add, show n1 + (j - n1) = j by omega] at this

/-- **Bytes copied by `memcpy`** as an image. -/
theorem Img.of_bytesOf {src dst : BitVec 64}
    (hcp : NativeRustcVm.BytesAt d' dst (NativeRustcArm.bytesOf d src n)) : Img d src d' dst n :=
  fun j hj b hb ↦ by
    have := hcp j (by simp [NativeRustcArm.bytesOf]; omega)
    rw [this]
    simp only [NativeRustcArm.bytesOf, List.getElem_map, List.getElem_range]
    rw [hb]; rfl

/-- **Unchanged bytes** as an image. -/
theorem Img.of_same (h : NativeRustcVm.Layout.Same d d' p n) : Img d p d' p n :=
  fun j hj b hb ↦ by rw [h j hj]; exact hb

/-- **One word written alike.** -/
theorem Img.of_word {w : UInt64} (h : NativeRustcVm.WordAt d p w)
    (h' : NativeRustcVm.WordAt d' q w) :
    Img d p d' q 8 := fun j hj b hb ↦ by
  have e := h j (by rw [NativeRustcVm.length_wordBytes]; exact hj)
  have e' := h' j (by rw [NativeRustcVm.length_wordBytes]; exact hj)
  rw [hb] at e
  rw [e', ← e]

theorem Img.bytesAt (h : Img d p d' q n) {o : Nat} {bs : List UInt8}
    (hb : NativeRustcVm.BytesAt d (p + BitVec.ofNat 64 o) bs) (hle : o + bs.length ≤ n) :
    NativeRustcVm.BytesAt d' (q + BitVec.ofNat 64 o) bs := fun i hi ↦ by
  have := hb i hi
  rw [NativeRustcVm.addr_add_add] at this ⊢
  exact h _ (by omega) _ this

theorem Img.bytesAt0 (h : Img d p d' q n) {bs : List UInt8} (hb : NativeRustcVm.BytesAt d p bs)
    (hle : bs.length ≤ n) : NativeRustcVm.BytesAt d' q bs := by
  have := h.bytesAt (o := 0) (by rw [NativeRustcVm.addr_add_zero]; exact hb) (by omega)
  rwa [NativeRustcVm.addr_add_zero] at this

theorem Img.bufEWAt (h : Img d p d' q n) {o N : Nat} {xs : List EW}
    (hb : NativeRustcVm.BufEWAt d (p + BitVec.ofNat 64 o) N xs) (hle : o + 8 + 16 * N ≤ n) :
    NativeRustcVm.BufEWAt d' (q + BitVec.ofNat 64 o) N xs := by
  obtain ⟨hl, hw, he⟩ := hb
  refine ⟨hl, h.bytesAt hw (by rw [NativeRustcVm.length_wordBytes]; omega), ?_⟩
  have e : ∀ x : BitVec 64, x + BitVec.ofNat 64 o + 8#64 = x + BitVec.ofNat 64 (o + 8) := fun x ↦
    NativeRustcVm.addr_add_add _ _ _
  rw [e] at he ⊢
  exact h.bytesAt he (by rw [NativeRustcVm.length_ewsBytes]; omega)

/-- **A claim but its bit weights** moves with its 768 bytes. -/
theorem ClaimAt.img {c : KeccakClaimW} (h : ClaimAt d p c) (hi : Img d p d' q 768) :
    ClaimAt d' q c :=
  ⟨hi.bytesAt0 h.1 (by rw [NativeRustcVm.length_ewBytes]; omega), hi.bufEWAt h.2.1 (by decide),
    hi.bufEWAt h.2.2 (by decide)⟩

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
