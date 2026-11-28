module

public import NativeRustcVmArm.Wire.PhaseM.Mem
public import NativeRustcVmArm.Spec.Keccak

/-!
# `phase_m`: the first level's nodes

`hash_run`: from the hashing's set-up (`b26`, the height to the frame's byte 32), each leaf hashed
by `keccak256_words::<hash_words's closure>` into the frame's byte 64 (`b27`) and its node, the
position and the digest, stored at the working area's byte `4096 + 40 i` (`b28`), to the climb
(`Climb0`).
-/

namespace NativeRustcVmArm.Wire.PhaseM

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.PhaseM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

@[expose] public section

/-- What holds from the hashing on. -/
structure Mid (m0 : MachineData) (B : List UInt8) (c : Nat) (count : Nat)
    (qs : List Nat) (height lw : Nat) (rows : List (List K)) (c6 : Nat) (d : Mem 64) : Prop where
  model : phaseM B c = climbFin B qs height lw rows c6
  len : qs.length = count
  cnt0 : 0 < count
  cnt : count ≤ 256
  qlt : ∀ q ∈ qs, q < 2 ^ 32
  h32 : height ≤ 32
  lw64 : lw ≤ 64
  ps0 : 0 < (sortD qs).length
  ps256 : (sortD qs).length ≤ 256
  rlen : rows.length = (sortD qs).length
  rw : ∀ r ∈ rows, r.length ≤ lw
  f56 : FW m0 d 56 lw.toUInt64
  f48 : FW m0 d 48 (UInt64.ofBitVec (wa m0 2048))
  f40 : FW m0 d 40 (UInt64.ofBitVec (wa m0 352512))
  f32 : FW m0 d 32 height.toUInt64
  qsW : WordsAt d (wa m0 0) (qs.map Nat.toUInt64)
  psW : WordsAt d (wa m0 2048) ((sortD qs).map Nat.toUInt64)
  lvW : LeavesAt d (wa m0 352512) (leavesOf lw rows)

/-- **Before leaf `i`'s hash** (`b27`). -/
structure HashSt [Host] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c k count : Nat)
    (qs : List Nat) (height lw : Nat) (rows : List (List K)) (c6 i : Nat) (st : MachineState) :
    Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PhaseM.b27Offset)
  base : Base m0 st.data
  mid : Mid m0 B c count qs height lw rows c6 st.data.dmem
  rd : ReaderAt st.data.dmem (rdr m0) bp B c6
  x21 : (st.data.regs.getXReg .X21).toNat = count
  x26 : (st.data.regs.getXReg .X26).toNat = (sortD qs).length
  x5 : (st.data.regs.getXReg .X5).toNat = lw
  x28 : (st.data.regs.getXReg .X28).toNat = 8 * lw
  x23 : (st.data.regs.getXReg .X23).toBitVec = wa m0 (2048 + 8 * i)
  x25 : (st.data.regs.getXReg .X25).toBitVec = wa m0 (4104 + 40 * i)
  x27 : (st.data.regs.getXReg .X27).toNat = (sortD qs).length - i
  x29 : (st.data.regs.getXReg .X29).toBitVec = wa m0 (352512 + 512 * i)
  ilt : i < (sortD qs).length
  nodes : NodesAt st.data.dmem (wa m0 4096) ((nodes0 qs lw rows).take i)

/-- **The climb's set-up** (`b29`). -/
structure Climb0 [Host] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c k count : Nat)
    (qs : List Nat) (height lw : Nat) (rows : List (List K)) (c6 : Nat) (st : MachineState) :
    Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PhaseM.b29Offset)
  base : Base m0 st.data
  mid : Mid m0 B c count qs height lw rows c6 st.data.dmem
  rd : ReaderAt st.data.dmem (rdr m0) bp B c6
  x21 : (st.data.regs.getXReg .X21).toNat = count
  x26 : (st.data.regs.getXReg .X26).toNat = (sortD qs).length
  x5 : (st.data.regs.getXReg .X5).toNat = lw
  nodes : NodesAt st.data.dmem (wa m0 4096) (nodes0 qs lw rows)

end

public section

theorem length_nodes0 {qs : List Nat} {lw : Nat} {rows : List (List K)}
    (h : rows.length = (sortD qs).length) : (nodes0 qs lw rows).length = (sortD qs).length := by
  simp [h]

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}

/-- **Frame words kept** by a change in the working area. -/
theorem FW.wa [Labels] (G : Geo m0 bp B) {d d' : Mem 64} {o n : Nat} (hon : o + n ≤ workBytes)
    (hs : SameOutside d d' (InRange (wa m0 o) n)) {f : Nat} {v : UInt64} (hf : f + 8 ≤ 192)
    (h : FW m0 d f v) : FW m0 d' f v :=
  h.keep hs fun i hi hq ↦ G.rgeo.not_frame (F := 192) (by omega)
    (.inr (.inr (NativeRustcVm.InRange.of_sub hq G.wOk.2 hon))) (by
      have hst := G.st
      have hb0 := Ring.base_toNat (m0 := m0) (F := 192) (by have := hst.2.1; omega)
      have := hst.2.1; have := m0.regs.SP.toNat_lt
      rw [Sym.inRange_iff (by rw [hb0]; omega), hb0, NativeRustcVm.addr_add_add,
        NativeRustcVm.toNat_add_ofNat (by rw [hb0]; omega), hb0]; omega)

/-- **What holds is kept** by a change in the stack, the cursor, the phase and parts `L` of the
working area between the positions and the leaves, the frame words given. -/
theorem Mid.keep [Labels] (G : Geo m0 bp B) {count : Nat} {qs : List Nat} {height lw : Nat}
    {rows : List (List K)} {c6 : Nat} {d d' : Mem 64} {L : List (Nat × Nat)}
    (h : Mid m0 B c count qs height lw rows c6 d) (hs : SameOutside d d' (Chg m0 L))
    (hL : ∀ p ∈ L, 4096 ≤ p.1 ∧ p.1 + p.2 ≤ 352512)
    (f56 : FW m0 d' 56 lw.toUInt64) (f48 : FW m0 d' 48 (UInt64.ofBitVec (wa m0 2048)))
    (f40 : FW m0 d' 40 (UInt64.ofBitVec (wa m0 352512))) (f32 : FW m0 d' 32 height.toUInt64) :
    Mid m0 B c count qs height lw rows c6 d' := by
  have hql := h.len
  have hps := h.ps256
  have hrl := h.rlen
  have hcnt := h.cnt
  have hW : workBytes = 483584 := workBytes_eq
  refine ⟨h.model, hql, h.cnt0, hcnt, h.qlt, h.h32, h.lw64, h.ps0, hps, hrl, h.rw, f56, f48, f40,
    f32, ?_, ?_, ?_⟩
  · refine NativeRustcVm.BytesAt.of_sameOutside h.qsW hs fun i hi ↦ ?_
    rw [NativeRustcVm.length_wordsBytes, List.length_map] at hi
    exact G.not_chg (o := 0) (n := 2048) (by omega)
      (fun p hp ↦ ⟨by have := hL p hp; omega, .inr (by have := hL p hp; omega)⟩) i (by omega)
  · refine NativeRustcVm.BytesAt.of_sameOutside h.psW hs fun i hi ↦ ?_
    rw [NativeRustcVm.length_wordsBytes, List.length_map] at hi
    exact G.not_chg (o := 2048) (n := 2048) (by omega)
      (fun p hp ↦ ⟨by have := hL p hp; omega, .inr (by have := hL p hp; omega)⟩) i (by omega)
  · refine leaves_keep h.lvW hs (fun x hx ↦ ?_) fun i hi ↦ ?_
    · simp only [leavesOf, List.mem_map] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      rw [length_paddedLeaf (h.rw r hr)]; exact h.lw64
    · rw [List.length_map] at hi
      exact G.not_chg (o := 352512) (n := 131072) (by omega)
        (fun p hp ↦ ⟨by have := hL p hp; omega, .inl (by have := hL p hp; omega)⟩) i (by omega)

end

end NativeRustcVmArm.Wire.PhaseM
