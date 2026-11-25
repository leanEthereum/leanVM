module

public import NativeRustcVm.Mem
public import NativeVm.Entry

/-!
# `leanvm_verify`'s caller, arch-independent

What `leanvm_verify(ctx)` needs of its caller beyond `NativeVm.Entry.CheckedEntryPre`, on the byte memory:
the checks it makes (`Aligned`: the decoded and the working areas nonzero and 8-aligned, the
bytecode 8-aligned when nonempty, the wire nonzero when nonempty; rustc's slices require them), and
the caller's areas (`usedRegions`: the context, the wire, the bytecode, the decoded and the
working areas, in bytes) apart from the verifier's stack and read-only data (`ApartFrom`).

The working area holds `WORK_WORDS` words, shared by `Work` and `DecodeWork`.
-/

namespace NativeRustcVm.Top

open NativeVm NativeVm.Entry
open NativeVm.Transcript (wd)

@[expose] public section

/-- `WORK_WORDS`: the working area's words the crate uses (`size_of::<Work>() / 8`). -/
def workAreaWords : Nat := 61944

/-- The working area's bytes the crate uses (`size_of::<Work>()`). -/
def workAreaBytes : Nat := 8 * workAreaWords

/-- The exact regions used after the entry checks succeed. -/
def usedRegions (ctx : UInt64) (a : Areas) (L n : Nat) : List Region :=
  [⟨ctx.toBitVec, 8 * NativeVm.Entry.ctxWords⟩, ⟨a.wire.toBitVec, L⟩, ⟨a.bytecode.toBitVec, 8 * n⟩,
    ⟨a.decoded.toBitVec, 8 * decodedWords L⟩, ⟨a.work.toBitVec, 8 * workWords⟩]

/-- The caller's declared regions, including the context and exact wire bytes. -/
def entryRegions (ctx : UInt64) (a : Areas) (L n : Nat) : List Region :=
  [⟨ctx.toBitVec, 8 * ctxWords⟩, ⟨a.wire.toBitVec, L⟩, ⟨a.bytecode.toBitVec, 8 * n⟩,
    ⟨a.decoded.toBitVec, 8 * a.decCount.toNat⟩, ⟨a.work.toBitVec, 8 * a.workCount.toNat⟩]

theorem usedRegions_cover {ctx : UInt64} {a : Areas} {L n : Nat} (hc : CountsOk a L n) {r : Region}
    (hr : r ∈ usedRegions ctx a L n) :
    ∃ s ∈ entryRegions ctx a L n, s.addr = r.addr ∧ r.size ≤ s.size := by
  simp only [usedRegions, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [entryRegions], rfl, Nat.le_refl _⟩
  · exact ⟨_, by simp [entryRegions], rfl, Nat.le_refl _⟩
  · exact ⟨_, by simp [entryRegions], rfl, Nat.le_refl _⟩
  · exact ⟨⟨a.decoded.toBitVec, 8 * a.decCount.toNat⟩, by simp [entryRegions], rfl,
      Nat.mul_le_mul_left 8 hc.2.2.1⟩
  · exact ⟨⟨a.work.toBitVec, 8 * a.workCount.toNat⟩, by simp [entryRegions], rfl,
      Nat.mul_le_mul_left 8 hc.2.2.2⟩

/-- Every region of positive size is apart from the `n` bytes from `b`. -/
def ApartFrom (rs : List Region) (b : BitVec 64) (n : Nat) : Prop :=
  ∀ r ∈ rs, 0 < r.size → Apart r.addr r.size b n

theorem ApartFrom.used {ctx : UInt64} {a : Areas} {L n k : Nat} {b : BitVec 64}
    (h : ApartFrom (entryRegions ctx a L n) b k)
    (hc : CountsOk a L n) : ApartFrom (usedRegions ctx a L n) b k := by
  intro r hr hp
  obtain ⟨s, hs, ha, hn⟩ := usedRegions_cover hc hr
  have h := h s hs (by omega)
  unfold Apart at h ⊢
  rw [ha] at h
  omega

/-- **The alignment `leanvm_verify` checks**: the decoded and the working areas nonzero and
8-aligned, the bytecode 8-aligned (and nonzero) when nonempty, the wire nonzero when nonempty. -/
structure Aligned (a : Areas) (L n : Nat) : Prop where
  dec : a.decoded ≠ 0 ∧ a.decoded.toNat % 8 = 0
  work : a.work ≠ 0 ∧ a.work.toNat % 8 = 0
  bytecode : 0 < n → a.bytecode ≠ 0 ∧ a.bytecode.toNat % 8 = 0
  wire : 0 < L → a.wire ≠ 0

/-- Every rejection check in `leanvm_verify`, in source order. -/
def Checks (a : Areas) (L n : Nat) : Prop := CountsOk a L n ∧ Aligned a L n

noncomputable instance (a : Areas) (L n : Nat) : Decidable (Checks a L n) :=
  Classical.propDecidable _

theorem workAreaWords_le : workAreaWords ≤ workWords := Nat.le_refl _

end

end NativeRustcVm.Top
