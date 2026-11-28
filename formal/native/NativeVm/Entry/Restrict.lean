module

public import NativeVm.Entry
public import NativeRustc.ReadRegions
public import NativeRustcVm.WordView

namespace NativeRustcVm

public section

theorem BytesAt.restrict {d : Mem 64} {a : BitVec 64} {bs : List UInt8}
    {regions : List (BitVec 64 × Nat)} (h : BytesAt d a bs) (ha : (a, bs.length) ∈ regions) :
    BytesAt (NativeRustc.restrictMemory d regions) a bs := by
  intro i hi
  rw [NativeRustc.restrictMemory_inside d ha hi]
  exact h i hi

theorem Mapped.restrict {d : Mem 64} {a : BitVec 64} {n : Nat}
    {regions : List (BitVec 64 × Nat)} (h : Mapped d a n) (ha : (a, n) ∈ regions) :
    Mapped (NativeRustc.restrictMemory d regions) a n := by
  intro i hi
  rw [NativeRustc.restrictMemory_inside d ha hi]
  exact h i hi

end

end NativeRustcVm

namespace NativeVm.Entry

open NativeRustc NativeRustcVm NativeVm.Transcript

public section

theorem restrictWord {mem : Mem 64} {base v : UInt64} {k n : Nat}
    {regions : List (BitVec 64 × Nat)} (h : wordView mem (wd base k) = some v)
    (ha : (base.toBitVec, 8 * n) ∈ regions) (hk : k < n) :
    wordView (restrictMemory mem regions) (wd base k) = some v := by
  apply WordAt.wordView
  intro i hi
  have hi8 : i < 8 := by simpa only [length_wordBytes] using hi
  rw [toBitVec_wd, addr_add_add, restrictMemory_inside mem ha (by omega)]
  have h := wordAt_of_wordView h i hi
  simpa only [toBitVec_wd, addr_add_add] using h

theorem restrictSome {mem : Mem 64} {base : UInt64} {k n : Nat}
    {regions : List (BitVec 64 × Nat)} (h : (wordView mem (wd base k)).isSome)
    (ha : (base.toBitVec, 8 * n) ∈ regions) (hk : k < n) :
    (wordView (restrictMemory mem regions) (wd base k)).isSome := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  exact Option.isSome_iff_exists.mpr ⟨v, restrictWord hv ha hk⟩

theorem EntryPre.restrict {mem : Mem 64} {ctx : UInt64} {a : Areas} {bytes : List UInt8}
    {bytecode : List UInt64} {pub : Vector UInt64 4} {regions : List (BitVec 64 × Nat)}
    (h : EntryPre mem ctx a bytes bytecode pub)
    (hctx : (ctx.toBitVec, 8 * ctxWords) ∈ regions)
    (hwire : (a.wire.toBitVec, bytes.length) ∈ regions)
    (hbc : (a.bytecode.toBitVec, 8 * bytecode.length) ∈ regions)
    (hdec : (a.decoded.toBitVec, 8 * a.decCount.toNat) ∈ regions)
    (hwork : (a.work.toBitVec, 8 * a.workCount.toNat) ∈ regions) :
    EntryPre (restrictMemory mem regions) ctx a bytes bytecode pub := by
  refine { h with
    toContextAt := { h.toContextAt with
      ctxSome := fun k hk ↦ restrictSome (h.ctxSome k hk) hctx hk
      wirePtr := restrictWord h.wirePtr hctx (by decide)
      wireLen := restrictWord h.wireLen hctx (by decide)
      bcPtr := restrictWord h.bcPtr hctx (by decide)
      bcLen := restrictWord h.bcLen hctx (by decide)
      pubWords := fun i hi ↦ restrictWord (h.pubWords i hi) hctx (by unfold ctxWords; omega)
      decPtr := restrictWord h.decPtr hctx (by decide)
      decCount := restrictWord h.decCount hctx (by decide)
      workPtr := restrictWord h.workPtr hctx (by decide)
      workCount := restrictWord h.workCount hctx (by decide) }
    wire := h.wire.restrict hwire
    bcWords := fun i hi ↦ restrictWord (h.bcWords i hi) hbc hi
    decSome := fun k hk ↦ restrictSome (h.decSome k hk) hdec hk
    workSome := fun k hk ↦ restrictSome (h.workSome k hk) hwork hk }

end

end NativeVm.Entry
