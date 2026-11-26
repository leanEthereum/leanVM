/-
  Rv64mc.Proof.Transcript.MerkleT

  `Transcript::merkle(root, block_length, queries, leaf_words)` is total (`specT`): from a transcript
  `TranscriptAtT` (`TranscriptReprT`) owned with its proof and in a caller's frame, the proof's Merkle openings
  `OpeningsT` (each opening's paths, each path's leaf and siblings, allocated and in windows), a result's slot of `24`
  bytes owned, in a window, 8-byte aligned, apart from the transcript and its proof, the root's `32` bytes in a window
  and the queries in a window unless none, it returns with the transcript `TranscriptAtT` and owned again, its
  proof's address kept, and, unless the slot holds `Err` (its first word the niche `-1`), the slot a vector
  (`VecReprT.VecT`) of slices each a path's leaf (`SliceKT`: allocated, in a window, 8-byte aligned), writing at most
  the slot and the opening offset besides what it allocates, or ends the run with `a0 = 2` where `MerklePath::root`,
  `alloc` or the capacity's check does. Safety only: the partial contract's leaves and transcript
  (`Spec/Transcript/Merkle.lean`) rest on `root`'s functional contract, which is not total. `log2_strict`'s two
  constant tables are an environment fact (`DataRef.InData env (tables L)`).

  Cut at the loop heads: the entry to the shape's check (`kept`), the shape's check (`loop1`, `L1Inv`), the
  positions' check (`loop2`, `L2Inv`), the checked flag (`mid_ok`), the roots' check (`loop3`, `L3Inv`), the
  capacity's check and `alloc` (`coll_ok`, `DInv`), the leaves' copy (`loop4`, `L4Inv`), the exit (`fin_ok`,
  `FInv`) and the error (`err_ok`, `EInv`). Each loop is `Total.loop` with the paths left as the measure. The memory
  every part keeps is `BaseM` (a frame writing only the opening offset before the slot's stores), carried across the
  calls and the buffer's stores by `baseM_call` and `baseM_fresh2`; the paths, allocated before the entry, are read
  in later memories through it (`keepLow`).

  ## Main definitions

  * `SliceKT`, `PathT`, `PathsT`, `OpeningsT`, `PreT`, `OkVec`, `PostT`, `specT`, `PostK`, `Ctx`, `tables`,
    `OffOut`, `BaseR`, `BaseM`, `EInv`, `Base`, `L1Inv`, `L2Inv`, `OpenT`, `L3Inv`, `DInv`, `L4Inv`, `FInv`

  ## Main results

  * `err_ok`, `loop1`, `loop2`, `keepLow`, `PathT.keep`, `baseM_call`, `loop3`, `mid_ok`, `cap_ok`, `coll_ok`,
    `copy_step`, `slices_of`, `baseM_fresh2`, `fin_ok`, `loop4`, `openT_of`, `kept`, `out_miss`, `total`
-/

import Rv64mc.Proof.Transcript.NextScalarsT
import Rv64mc.Proof.Merkle.RootT
import Rv64mc.Proof.Runtime.MemcmpT
import Rv64mc.Spec.Transcript.Merkle
import Rv64mc.Gen.Tmpl.Verifier.Transcript.Transcript.Merkle

namespace Rv64mc.Proof.Transcript.MerkleT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Transcript Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT RawVecT BufT)
open Rv64mc.Proof.Transcript.SpongeReprT Rv64mc.Proof.Transcript.TranscriptReprT
open Rv64mc.Proof.Transcript.NextScalarsT (ne_of_toNat_lt sret_spongeT vecT_stores)
open Rv64mc.Gen.Verifier.Transcript.Transcript.Merkle (Link tmpl)

/-- A slice `&[K]` at `s` (pointer, length): empty, or its words allocated, in a window, 8-byte aligned. -/
def SliceKT (env : Env) (m : MachineState) (s : Word) : Prop :=
  (m.getMem (s + 8#64)).toNat = 0 ∨
    (env.Live m (m.getMem s) (8 * (m.getMem (s + 8#64)).toNat) ∧
      InWin env (m.getMem s) (8 * (m.getMem (s + 8#64)).toNat) ∧ (m.getMem s).toNat % 8 = 0)

/-- A `MerklePath` at `a`, for safety: its leaf (`Vec<K>` at `0`) a `SliceKT` at `a + 8`, its siblings' digests (the
    `Vec<Digest>` at `24`), unless none, allocated and in a window. -/
def PathT (env : Env) (m : MachineState) (a : Word) : Prop :=
  SliceKT env m (a + 8#64) ∧
  ((m.getMem (a + 40#64)).toNat = 0 ∨
    (env.Live m (m.getMem (a + 32#64)) (32 * (m.getMem (a + 40#64)).toNat) ∧
      InWin env (m.getMem (a + 32#64)) (32 * (m.getMem (a + 40#64)).toNat)))

/-- A `Vec<MerklePath>` at `o`: no paths, or its buffer allocated, in a window, 8-byte aligned, each path `PathT`. -/
def PathsT (env : Env) (m : MachineState) (o : Word) : Prop :=
  (m.getMem (o + 16#64)).toNat = 0 ∨
    ((m.getMem (o + 8#64)).toNat % 8 = 0 ∧ env.Live m (m.getMem (o + 8#64)) (56 * (m.getMem (o + 16#64)).toNat) ∧
      InWin env (m.getMem (o + 8#64)) (56 * (m.getMem (o + 16#64)).toNat) ∧
      ∀ j < (m.getMem (o + 16#64)).toNat, PathT env m (m.getMem (o + 8#64) + BitVec.ofNat 64 (56 * j)))

/-- The proof's Merkle openings (`Vec<Vec<MerklePath>>` at `q + 24`): none, or its buffer allocated, in a window,
    8-byte aligned, each opening `PathsT`. -/
def OpeningsT (env : Env) (m : MachineState) (q : Word) : Prop :=
  (m.getMem (q + 40#64)).toNat = 0 ∨
    ((m.getMem (q + 32#64)).toNat % 8 = 0 ∧ env.Live m (m.getMem (q + 32#64)) (24 * (m.getMem (q + 40#64)).toNat) ∧
      InWin env (m.getMem (q + 32#64)) (24 * (m.getMem (q + 40#64)).toNat) ∧
      ∀ k < (m.getMem (q + 40#64)).toNat, PathsT env m (m.getMem (q + 32#64) + BitVec.ofNat 64 (24 * k)))

/-- The total precondition: the transcript at `a1` `TranscriptAtT`, owned with its proof and in a caller's frame,
    its proof's openings `OpeningsT`; the result's slot (`24` bytes) owned, in a window, 8-byte aligned, apart from
    the transcript and its proof; the root's `32` bytes in a window; the queries (`a4`, `a5` words), unless none, in
    a window and 8-byte aligned. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  TranscriptAtT env m (regs .x11) ∧ OwnedT env m (regs .x2) (regs .x11) ∧ (regs .x2).toNat ≤ (regs .x11).toNat ∧
    OpeningsT env m (m.getMem (regs .x11 + 328#64)) ∧
    InWin env (regs .x10) Layouts.ResultVecE.byteSize ∧ (regs .x10).toNat % 8 = 0 ∧
    env.Owned m (regs .x2) (regs .x10) Layouts.ResultVecE.byteSize ∧
    Apart (regs .x10) Layouts.ResultVecE.byteSize (regs .x11) Layouts.Transcript.byteSize ∧
    Apart (regs .x10) Layouts.ResultVecE.byteSize (m.getMem (regs .x11 + 328#64)) Layouts.Proof.byteSize ∧
    InWin env (regs .x12) Layouts.Digest.byteSize ∧
    ((regs .x15).toNat = 0 ∨ (InWin env (regs .x14) (8 * (regs .x15).toNat) ∧ (regs .x14).toNat % 8 = 0))

/-- `PreT`'s facts the parts carry whole. -/
structure Ctx (env : Env) (top : Word) (regs : Reg → Word) (m : MachineState) : Prop where
  tT : TranscriptAtT env m (regs .x11)
  tO : OwnedT env m top (regs .x11)
  tS : top.toNat ≤ (regs .x11).toNat
  oP : OpeningsT env m (m.getMem (regs .x11 + 328#64))
  wS : InWin env (regs .x10) 24
  aS : (regs .x10).toNat % 8 = 0
  oS : env.Owned m top (regs .x10) 24
  apST : Apart (regs .x10) 24 (regs .x11) Layouts.Transcript.byteSize
  apSP : Apart (regs .x10) 24 (m.getMem (regs .x11 + 328#64)) Layouts.Proof.byteSize
  wR : InWin env (regs .x12) 32
  wQ : (regs .x15).toNat = 0 ∨ (InWin env (regs .x14) (8 * (regs .x15).toNat) ∧ (regs .x14).toNat % 8 = 0)

/-- Unless the slot holds `Err` (its first word the niche `-1`), the slot a vector of slices, each a `SliceKT`. -/
def OkVec (env : Env) (regs : Reg → Word) (m' : MachineState) : Prop :=
  m'.getMem (regs .x10) ≠ 18446744073709551615#64 →
    VecT env m' (regs .x10) 16 ∧ ∀ k < (m'.getMem (regs .x10 + 16#64)).toNat,
      SliceKT env m' (m'.getMem (regs .x10 + 8#64) + BitVec.ofNat 64 (16 * k))

/-- The total postcondition: the transcript `TranscriptAtT` and owned again, its proof's address kept, `OkVec`. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  TranscriptAtT env m' (regs .x11) ∧ OwnedT env m' (regs .x2) (regs .x11) ∧
    m'.getMem (regs .x11 + 328#64) = m.getMem (regs .x11 + 328#64) ∧ OkVec env regs m'

/-- **The total contract of `Transcript::merkle`**: `PreT` to `PostT`, writing at most the slot and the opening
    offset (`Merkle.Out`, the partial contract's), or ending the run with `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) Merkle.Out (Stop := AbortStop)

/-- What the run gives, from which `PostT` follows with the frame. -/
def PostK (env : Env) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  OkVec env regs m'

/-- The two constant tables `log2_strict` reads (the de Bruijn multiplier and its 64-byte index). -/
abbrev tables (L : Link) : List (DataRef × List Word) :=
  [(L.d_c8_14ca7de5, Gen.Verifier.Transcript.Transcript.Merkle.d_c8_14ca7de5_words),
    (L.d_c64_b1d69b10, Gen.Verifier.Transcript.Transcript.Merkle.d_c64_b1d69b10_words)]

/-- What the body writes before the slot's stores: the opening offset. -/
def OffOut (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop := b = regs .x11 + 344#64

/-- What every part keeps of the registers: the stack pointer, the registers no part writes. -/
def BaseR (top : Word) (regs : Reg → Word) (R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551536#64 ∧
    R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧
    R .x26 = regs .x26 ∧ R .x27 = regs .x27

/-- What every part keeps of the memory: the frame (writing at most the opening offset), the code, the static data,
    the saved registers' slots. -/
def BaseM (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (M : MachineState) : Prop :=
  env.Frame top (OffOut regs m) m M ∧ M.code = m.code ∧ env.Static M ∧
    M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20

/-- The error's path (instruction 132): `BaseR`, `BaseM`, the slot's address in `x10`. -/
def EInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  BaseR top regs R ∧ BaseM env ret top regs m M ∧ R .x10 = regs .x10

set_option hygiene false in
/-- `BaseR` and the slot's register at a stop, the memory's `BaseM` given. -/
local macro "base_regs" hm:term : term =>
  `(⟨⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT,
    by rv_closeT⟩, $hm, by rv_closeT⟩)

/-- A byte of a 64-byte table in a window, at an offset `z >>> 58`, is in a window. -/
theorem byte_in {B : Word} (hB : inWindow B 64 = true) (z : Word) : inWindow (B + z >>> 58) 1 = true := by
  have hz : (z >>> 58).toNat < 64 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := z.isLt; omega
  rw [inWindow_iff] at hB ⊢
  rw [BitVec.toNat_add]; omega

/-- `24 x` as the code computes it. -/
theorem shl24 {x : Word} (h : 24 * x.toNat < 2 ^ 64) : (x <<< 4 + x <<< 3).toNat = 24 * x.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq]; omega

/-- `56 x` as the code computes it. -/
theorem shl56 {x : Word} (h : 56 * x.toNat < 2 ^ 64) : (x <<< 6 - x <<< 3).toNat = 56 * x.toNat := by
  rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq]; omega

/-- `8 x` as the code computes it. -/
theorem shl8 {x : Word} (h : 8 * x.toNat < 2 ^ 64) : (x <<< 3).toNat = 8 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

/-- A frame with a smaller `out`. -/
theorem frame_widen {env : Env} {top : Word} {out out' : Word → Prop} {m M : MachineState}
    (h : env.Frame top out m M) (hs : ∀ b, out b → out' b) : env.Frame top out' m M :=
  ⟨h.1, h.2.1, fun a ha => h.2.2 a fun hw => ha (hw.imp_right (·.imp_right (·.imp_right (hs a))))⟩

/-- The opening offset is in `Merkle.Out`. -/
theorem offOut_out {regs : Reg → Word} {m : MachineState} (b : Word) (h : OffOut regs m b) : Merkle.Out regs m b :=
  Or.inr h

set_option hygiene false in
/-- A word `top + c` of the frame, as a number. -/
local macro "tn" : tactic => `(tactic| (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))

set_option rv_sym.heap true in
/-- On an error: `Err` into the slot (the niche, the error's code), the return. -/
theorem err_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostK env) Merkle.Out ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 80 ≤ need) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hC : Ctx env top regs m) :
    ∀ R M, EInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 132, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  have hF := frame_widen hinv.2.1.1 offOut_out
  rv_introT hinv
  have hwS := hC.wS
  have haS := hC.aS
  have hoS := hC.oS
  rv_symT hp with [(by omega : env.stackLimit.toNat + 80 ≤ top.toNat)]
  rv_symT hp with [(by omega : env.stackLimit.toNat + 80 ≤ top.toNat)]
  · have hlS := hwS.lt
    have o0 : Merkle.Out regs m (regs .x10) := Or.inl ⟨Nat.le_refl _, by simp only [Layouts.ResultVecE.byteSize]; omega⟩
    have o8 : Merkle.Out regs m (regs .x10 + 8#64) := Or.inl (by
      simp only [InRange, Layouts.ResultVecE.byteSize]; rw [toNat_add_ofNat (by omega)]; omega)
    exact Tactic.frame_out (Tactic.frame_out hF o0 (hwS.ne_next (Nat.le_refl _) (by omega)))
      o8 (hwS.ne_next_add (o := 8) (by omega))
  · intro h; exact absurd rfl h

/-- The registers every loop keeps of the entry: `BaseR`, `BaseM`, the slot in `x10`. -/
def Base (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  BaseR top regs R ∧ BaseM env ret top regs m M ∧ R .x10 = regs .x10

/-- The first loop's head (instruction 82), `k` paths left of the opening `o`'s `n` at `P`: the shape's check. -/
def L1Inv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (o : Word) (k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  Base env ret top regs m R M ∧ R .x5 = regs .x11 ∧ R .x6 = m.getMem (o + 16#64) ∧ R .x9 = o ∧
    R .x11 = m.getMem (o + 8#64) ∧ R .x12 = regs .x12 ∧ R .x13 = m.getMem (o + 16#64) <<< 3 ∧
    R .x14 = regs .x14 ∧ R .x15 = regs .x15 ∧ R .x16 = regs .x16 ∧ R .x17 = m.getMem (o + 16#64) <<< 6 ∧
    (R .x28).toNat = 56 * k ∧
    R .x29 = m.getMem (o + 8#64) + BitVec.ofNat 64 (56 * ((m.getMem (o + 16#64)).toNat - k)) ∧
    k ≤ (m.getMem (o + 16#64)).toNat

/-- The second loop's head (instruction 112), `k` paths left: the positions' check. -/
def L2Inv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (o : Word) (k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  Base env ret top regs m R M ∧ R .x5 = regs .x11 ∧ R .x9 = o ∧
    R .x11 = m.getMem (o + 8#64) ∧ R .x12 = regs .x12 ∧ R .x13 = m.getMem (o + 16#64) <<< 3 ∧
    R .x15 = regs .x15 ∧ regs .x15 = m.getMem (o + 16#64) ∧ R .x17 = m.getMem (o + 16#64) <<< 6 ∧
    (R .x6).toNat = 56 * k ∧ (R .x16).toNat = 8 * k ∧
    R .x7 = m.getMem (o + 8#64) + BitVec.ofNat 64 (56 * ((m.getMem (o + 16#64)).toNat - k)) ∧
    R .x14 = regs .x14 + BitVec.ofNat 64 (8 * ((m.getMem (o + 16#64)).toNat - k)) ∧
    k ≤ (m.getMem (o + 16#64)).toNat

/-- The facts of the opening `o` the loops read: its header in a window, 8-byte aligned, allocated, its paths. -/
structure OpenT (env : Env) (m : MachineState) (o : Word) : Prop where
  w : InWin env o 24
  a : o.toNat % 8 = 0
  l : env.Live m o 24
  ps : PathsT env m o

/-- The paths' bytes do not wrap. -/
theorem OpenT.b56 {env : Env} {m : MachineState} {o : Word} (h : OpenT env m o) :
    56 * (m.getMem (o + 16#64)).toNat < 2 ^ 64 := by
  rcases h.ps with h | ⟨-, -, h, -⟩
  · omega
  · have := h.lt; omega

/-- Two offsets added in turn. -/
theorem add_ofNat_add (a : Word) (x y : Nat) :
    a + BitVec.ofNat 64 x + BitVec.ofNat 64 y = a + BitVec.ofNat 64 (x + y) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

set_option rv_sym.heap true in
/-- **The shape's check**: each path's leaf of `leaf_words` words and `height` siblings, else the error. -/
theorem loop1 (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} {o : Word} (_hstk : env.stackLimit.toNat + need ≤ top.toNat) (_hn : 80 ≤ need)
    (hW : Windows env top m) (hO : OpenT env m o)
    (herr : ∀ R M, EInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 132, ret, top⟩ :: rest, R, M⟩)
    (hnext : ∀ R M, L2Inv env ret top regs m o (m.getMem (o + 16#64)).toNat R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 112, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, L1Inv env ret top regs m o k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 82, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (L1Inv env ret top regs m o) fun k R M hI ih => ?_
  have hBM := hI.1.2.1
  have hPw : (m.getMem (o + 16#64)).toNat = 0 ∨
      (InWin env (m.getMem (o + 8#64)) (56 * (m.getMem (o + 16#64)).toNat) ∧ (m.getMem (o + 8#64)).toNat % 8 = 0) :=
    hO.ps.imp id fun h => ⟨h.2.2.1, h.1⟩
  have hb56 : 56 * (m.getMem (o + 16#64)).toNat < 2 ^ 64 := by
    rcases hPw with h | ⟨h, -⟩
    · omega
    · have := h.lt; omega
  have hx29 : (m.getMem (o + 8#64) + BitVec.ofNat 64 (56 * ((m.getMem (o + 16#64)).toNat - k))).toNat =
      (m.getMem (o + 8#64)).toNat + 56 * ((m.getMem (o + 16#64)).toNat - k) := by
    rcases hPw with h | ⟨h, -⟩
    · rw [show (m.getMem (o + 16#64)).toNat - k = 0 by omega]; simp
    · exact toNat_add_ofNat (by have := h.lt; omega)
  rv_introT hI
  rv_symT hp stop [84, 112, 132] with [(by omega : env.stackLimit.toNat + 80 ≤ top.toNat)]
  -- the opening's length is not the queries'
  · exact herr _ _ (base_regs hBM)
  -- every path checked: on to the positions' check
  · refine hnext _ _ ⟨base_regs hBM, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Nat.le_refl _⟩
    iterate 6 · rv_closeT
    · exact hc.symm
    · rv_closeT
    · simp only [Tactic.rf]; exact shl56 hb56
    · simp only [Tactic.rf]; rw [← hc]; exact shl8 (by omega)
    · simp only [Tactic.rf, Nat.sub_self, Nat.mul_zero]; exact (BitVec.add_zero _).symm
    · simp only [Tactic.rf, Nat.sub_self, Nat.mul_zero]; exact (BitVec.add_zero _).symm
  -- a path left
  · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero fun h => hc (BitVec.eq_of_toNat_eq (by rw [hI_29, h]; rfl))
    clear hc
    obtain ⟨hPw', hPa⟩ := hPw.resolve_left (by omega)
    have w16 := hPw'.dword_add (k := 16) hW hPa hx29 (by omega) (by omega)
    have w40 := hPw'.dword_add (k := 40) hW hPa hx29 (by omega) (by omega)
    rv_symT hp stop [82, 132] with [(by omega : env.stackLimit.toNat + 80 ≤ top.toNat)]
    any_goals (first | exact w16.1 | exact w40.1)
    · exact herr _ _ (base_regs hBM)
    · refine ih (k - 1) _ _ (by omega) ⟨base_regs hBM, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
      iterate 10 · rv_closeT
      · simp only [Tactic.rf]; rw [BitVec.toNat_add, hI_29]; simp; omega
      · simp only [Tactic.rf]; rw [add_ofNat_add]; congr 2; omega
    · exact herr _ _ (base_regs hBM)

set_option rv_sym.heap true in
/-- **The positions' check**: each path's leaf index the query's, else the error. -/
theorem loop2 (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} {o : Word} (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 80 ≤ need)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hO : OpenT env m o)
    (hQ : (regs .x15).toNat = 0 ∨ (InWin env (regs .x14) (8 * (regs .x15).toNat) ∧ (regs .x14).toNat % 8 = 0))
    (herr : ∀ R M, EInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 132, ret, top⟩ :: rest, R, M⟩)
    (hnext : ∀ R M, L2Inv env ret top regs m o 0 R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 154, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, L2Inv env ret top regs m o k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 112, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (L2Inv env ret top regs m o) fun k R M hI ih => ?_
  have hBM := hI.1.2.1
  have hPw : (m.getMem (o + 16#64)).toNat = 0 ∨
      (InWin env (m.getMem (o + 8#64)) (56 * (m.getMem (o + 16#64)).toNat) ∧ (m.getMem (o + 8#64)).toNat % 8 = 0) :=
    hO.ps.imp id fun h => ⟨h.2.2.1, h.1⟩
  rv_introT hI
  rv_symT hp stop [114, 154] with [(by omega : env.stackLimit.toNat + 80 ≤ top.toNat)]
  -- every position checked
  · refine hnext _ _ ⟨base_regs hBM, ?_, ?_, ?_, ?_, ?_, ?_, hI_25, ?_, ?_, ?_, ?_, ?_, Nat.zero_le _⟩
    iterate 7 · rv_closeT
    · simp only [Tactic.rf]; rw [hc]; rfl
    · have hk0 : k = 0 := by have := congrArg BitVec.toNat hc; rw [hI_27] at this; simpa using this
      subst hk0; simp only [Tactic.rf]; exact hI_28
    · have hk0 : k = 0 := by have := congrArg BitVec.toNat hc; rw [hI_27] at this; simpa using this
      subst hk0; rv_closeT
    · have hk0 : k = 0 := by have := congrArg BitVec.toNat hc; rw [hI_27] at this; simpa using this
      subst hk0; rv_closeT
  -- a path left
  · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero fun h => hc (BitVec.eq_of_toNat_eq (by rw [hI_27, h]; rfl))
    clear hc
    obtain ⟨hPw', hPa⟩ := hPw.resolve_left (by omega)
    rw [hI_25] at hQ
    obtain ⟨hQw, hQa⟩ := hQ.resolve_left (by omega)
    have hx7 : (m.getMem (o + 8#64) + BitVec.ofNat 64 (56 * ((m.getMem (o + 16#64)).toNat - k))).toNat =
        (m.getMem (o + 8#64)).toNat + 56 * ((m.getMem (o + 16#64)).toNat - k) :=
      toNat_add_ofNat (by have := hPw'.lt; omega)
    have hx14 : (regs .x14 + BitVec.ofNat 64 (8 * ((m.getMem (o + 16#64)).toNat - k))).toNat =
        (regs .x14).toNat + 8 * ((m.getMem (o + 16#64)).toNat - k) :=
      toNat_add_ofNat (by have := hQw.lt; omega)
    have w48 := hPw'.dword_add (k := 48) hW hPa hx7 (by omega) (by omega)
    have wq := hQw.dword_add (k := 0) hW hQa hx14 (by omega) (by omega)
    rv_symT hp stop [112, 132] with [(by omega : env.stackLimit.toNat + 80 ≤ top.toNat)]
    · exact herr _ _ (base_regs hBM)
    · refine ih (k - 1) _ _ (by omega) ⟨base_regs hBM, ?_, ?_, ?_, ?_, ?_, ?_, hI_25, ?_, ?_, ?_, ?_, ?_, by omega⟩
      iterate 7 · rv_closeT
      · simp only [Tactic.rf]; rw [BitVec.toNat_add, hI_27]; simp; omega
      · simp only [Tactic.rf]; rw [BitVec.toNat_add, hI_28]; simp; omega
      · simp only [Tactic.rf]; rw [add_ofNat_add]; congr 2; omega
      · simp only [Tactic.rf]; rw [add_ofNat_add]; congr 2; omega
    · exact herr _ _ (base_regs hBM)

/-- The third loop's head (instruction 162), `k` paths left: each path's root against the root. -/
def L3Inv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (o : Word) (k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  Base env ret top regs m R M ∧ R .x8 = regs .x12 ∧ R .x9 = o ∧
    R .x11 = m.getMem (o + 8#64) + BitVec.ofNat 64 (56 * ((m.getMem (o + 16#64)).toNat - k)) ∧
    (R .x18).toNat = 56 * k ∧ k ≤ (m.getMem (o + 16#64)).toNat

/-- The leaves' collection (instruction 204): the paths' pointer and count. -/
def DInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (o : Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  Base env ret top regs m R M ∧ R .x11 = m.getMem (o + 8#64) ∧ R .x15 = m.getMem (o + 16#64)

/-- A word allocated at entry is kept by a frame writing only the opening offset, the transcript in a caller's
    frame. -/
theorem keepLow {env : Env} {top : Word} {regs : Reg → Word} {m M : MachineState}
    (hF : env.Frame top (OffOut regs m) m M) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hT : top.toNat ≤ (regs .x11).toNat) (hTl : (regs .x11).toNat + 360 < 2 ^ 64) (hW : Windows env top m)
    (hlim : env.stackLimit.toNat ≤ top.toNat) {a : Word}
    (ha : a.toNat < (env.next m).toNat) : M.getMem a = m.getMem a := by
  have := env.layout
  have := hW.heapEnd_le
  have := hW.nextAddr_ge
  refine hF.getMem_below_next hnx ha fun h => ?_
  have e : (regs .x11 + 344#64).toNat = (regs .x11).toNat + 344 := toNat_add_ofNat (by omega)
  have := congrArg BitVec.toNat h
  unfold OffOut at h
  rw [h, e] at ha
  have := hF.2.1
  omega

/-- A path allocated at entry keeps `PathT` in a memory agreeing on its words, `NEXT` not lower. -/
theorem PathT.keep {env : Env} {m M : MachineState} {a : Word} (h : PathT env m a)
    (hk : ∀ c : Nat, c = 8 ∨ c = 16 ∨ c = 32 ∨ c = 40 → M.getMem (a + BitVec.ofNat 64 c) = m.getMem (a + BitVec.ofNat 64 c))
    (hn : (env.next m).toNat ≤ (env.next M).toNat) : PathT env M a := by
  have h8 := hk 8 (by omega)
  have h16 := hk 16 (by omega)
  have h32 := hk 32 (by omega)
  have h40 := hk 40 (by omega)
  have e : a + 8#64 + 8#64 = a + 16#64 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨hl, hs⟩ := h
  unfold PathT
  unfold SliceKT at hl ⊢
  unfold Env.Live at hl hs
  refine ⟨?_, ?_⟩
  · rw [e, show (16#64 : Word) = BitVec.ofNat 64 16 from rfl, h16, show (8#64 : Word) = BitVec.ofNat 64 8 from rfl,
      h8]
    rw [e] at hl
    unfold Env.Live
    exact hl.imp id fun ⟨h1, h2, h3⟩ => ⟨by omega, h2, h3⟩
  · rw [show (40#64 : Word) = BitVec.ofNat 64 40 from rfl, h40, show (32#64 : Word) = BitVec.ofNat 64 32 from rfl,
      h32]
    unfold Env.Live
    exact hs.imp id fun ⟨h1, h2⟩ => ⟨by omega, h2⟩

/-- The leaf's conjunct of `RootT.PreT`, from `SliceKT` of the path's leaf. -/
theorem SliceKT.leaf {env : Env} {m : MachineState} {a : Word} (h : SliceKT env m (a + 8#64)) :
    (m.getMem (a + 16#64)).toNat = 0 ∨
      (env.Live m (m.getMem (a + 8#64)) (8 * (m.getMem (a + 16#64)).toNat) ∧
        InWin env (m.getMem (a + 8#64)) (8 * (m.getMem (a + 16#64)).toNat)) := by
  have e : a + 8#64 + 8#64 = a + 16#64 := by rw [BitVec.add_assoc]; rfl
  unfold SliceKT at h
  rw [e] at h
  exact h.imp id fun h => ⟨h.1, h.2.1⟩

/-- A digest at the stack pointer (`top - 80`) lies below the saved registers' slots. -/
theorem digestOut_low {top b : Word} (ht : 80 ≤ top.toNat) (hal : top.toNat % 16 = 0)
    (h : Spec.Hash.DigestOut (top + 18446744073709551536#64) b) : top.toNat - 80 ≤ b.toNat ∧ b.toNat < top.toNat - 48 := by
  have h2 : (top + 18446744073709551536#64).toNat = top.toNat - 80 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  simp only [Spec.Hash.DigestOut, DwordsOf, InRange, toNat_alignToDword, Layouts.Digest.byteSize, h2] at h
  omega

/-- **`BaseM` across a call** from the stack pointer that writes at most below the saved registers' slots. -/
theorem baseM_call {env : Env} {ret top : Word} {regs : Reg → Word} {m M m1 : MachineState} {out : Word → Prop}
    (hB : BaseM env ret top regs m M) (hlim : env.stackLimit.toNat + 80 ≤ top.toNat)
    (hf : env.Frame (top + 18446744073709551536#64) out M m1)
    (hout : ∀ b, out b → top.toNat - 80 ≤ b.toNat ∧ b.toNat < top.toNat - 48) (hc : m1.code = M.code)
    (hs : env.Static m1) : BaseM env ret top regs m m1 := by
  obtain ⟨hF, hcM, -, h1, h2, h3, h4, h5, h6⟩ := hB
  have hsp : (top + 18446744073709551536#64).toNat = top.toNat - 80 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hsl : ∀ c : Nat, 0 < c → c ≤ 48 → m1.getMem (top + BitVec.ofNat 64 (2 ^ 64 - c)) =
      M.getMem (top + BitVec.ofNat 64 (2 ^ 64 - c)) := fun c hc0 hc1 => by
    have e : (top + BitVec.ofNat 64 (2 ^ 64 - c)).toNat = top.toNat - c := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    exact hf.getMem_above (by rw [hsp]; omega) (by rw [e, hsp]; omega) fun h => by
      have := hout _ h; rw [e] at this; omega
  refine ⟨Env.Frame.trans hF hf (by rw [hsp]; omega) fun b hb => Or.inl ⟨by have := hout b hb; omega,
    by have := hout b hb; omega⟩, hc.trans hcM, hs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (18446744073709551608#64 : Word) = BitVec.ofNat 64 (2 ^ 64 - 8) from rfl, hsl 8 (by omega) (by omega)]
    exact h1
  · rw [show (18446744073709551600#64 : Word) = BitVec.ofNat 64 (2 ^ 64 - 16) from rfl,
      hsl 16 (by omega) (by omega)]
    exact h2
  · rw [show (18446744073709551592#64 : Word) = BitVec.ofNat 64 (2 ^ 64 - 24) from rfl,
      hsl 24 (by omega) (by omega)]
    exact h3
  · rw [show (18446744073709551584#64 : Word) = BitVec.ofNat 64 (2 ^ 64 - 32) from rfl,
      hsl 32 (by omega) (by omega)]
    exact h4
  · rw [show (18446744073709551576#64 : Word) = BitVec.ofNat 64 (2 ^ 64 - 40) from rfl,
      hsl 40 (by omega) (by omega)]
    exact h5
  · rw [show (18446744073709551568#64 : Word) = BitVec.ofNat 64 (2 ^ 64 - 48) from rfl,
      hsl 48 (by omega) (by omega)]
    exact h6

set_option rv_sym.heap true in
/-- **The roots' check**, when the transcript is checked: each path's root, then `memcmp` against the root. -/
theorem loop3 (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needR needC : Nat} (hnR : 80 + needR ≤ need) (hnC : 80 + needC ≤ need)
    (hro : Merkle.RootT.specT env p L.root.idx needR) (hmc : Runtime.MemcmpT.MemcmpSpecT env p L.memcmp.idx needC)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} {o : Word} (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hO : OpenT env m o) (hC : Ctx env top regs m)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (herr : ∀ R M, EInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 132, ret, top⟩ :: rest, R, M⟩)
    (hnext : ∀ R M, DInv env ret top regs m o R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 204, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, L3Inv env ret top regs m o k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 162, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (L3Inv env ret top regs m o) fun k R M hI ih => ?_
  have hBM := hI.1.2.1
  have hPw : (m.getMem (o + 16#64)).toNat = 0 ∨
      (InWin env (m.getMem (o + 8#64)) (56 * (m.getMem (o + 16#64)).toNat) ∧ (m.getMem (o + 8#64)).toNat % 8 = 0) :=
    hO.ps.imp id fun h => ⟨h.2.2.1, h.1⟩
  have hTl := hC.tT.2.1.lt
  have hTs := hC.tS
  have hOw := hO.w
  have hOl := hO.l
  unfold Env.Live at hOl
  have k8 := keepLow hBM.1 hnx hTs hTl hW (by omega) (a := o + 8#64)
    (by rw [toNat_add_ofNat (by have := hOw.lt; omega)]; omega)
  have k16 := keepLow hBM.1 hnx hTs hTl hW (by omega) (a := o + 16#64)
    (by rw [toNat_add_ofNat (by have := hOw.lt; omega)]; omega)
  rv_introT hI
  rv_symT hp stop [164, 204] with [hL, (by omega : env.stackLimit.toNat + 80 ≤ top.toNat)]
  -- every root checked
  · exact hnext _ _ ⟨base_regs hBM, by simp only [Tactic.rf]; exact k8, by simp only [Tactic.rf]; exact k16⟩
  -- a path left: its root
  · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero fun h => hc (BitVec.eq_of_toNat_eq (by rw [hI_22, h]; rfl))
    clear hc
    obtain ⟨hPa, hPl, hPw', hPs⟩ := hO.ps.resolve_left (by omega)
    unfold Env.Live at hPl
    have hPlt := hPw'.lt
    have hx : (m.getMem (o + 8#64) + BitVec.ofNat 64 (56 * ((m.getMem (o + 16#64)).toNat - k))).toNat =
        (m.getMem (o + 8#64)).toNat + 56 * ((m.getMem (o + 16#64)).toNat - k) := toNat_add_ofNat (by omega)
    have hpm := (hPs _ (by omega : (m.getMem (o + 16#64)).toNat - k < (m.getMem (o + 16#64)).toNat)).keep
      (M := M) (fun c hc => keepLow hBM.1 hnx hTs hTl hW (by omega)
        (by rw [toNat_add_ofNat (by omega), hx]; rcases hc with hc | hc | hc | hc <;> subst hc <;> omega))
      hBM.1.1
    have hnM := hBM.1.1
    have hwR := hC.wR
    rv_symT hp stop [174] with [hL, (by omega : env.stackLimit.toNat + 80 ≤ top.toNat)] using [hro]
    · exact hpm.1.leaf
    have hB1 := baseM_call hBM (by omega) hret1_14 (fun b h => digestOut_low (by omega) hal h) hret1_16 hret1_15
    rv_symT hp stop [162, 132] with [hL, (by omega : env.stackLimit.toNat + 80 ≤ top.toNat)] using [hmc]
    all_goals have hB2 := baseM_call hB1 (by omega) hret1_14 (fun b h => h.elim) hret1_17 hret1_15
    · refine ih (k - 1) _ _ (by omega) ⟨base_regs hB2, ?_, ?_, ?_, ?_, by omega⟩
      iterate 2 · rv_closeT
      · simp only [Tactic.rf]; rw [add_ofNat_add]; congr 2; omega
      · simp only [Tactic.rf]; rw [BitVec.toNat_add, hI_22]; simp; omega
    · exact herr _ _ (base_regs hB2)

set_option rv_sym.heap true in
/-- After the positions' check: the roots' check when the transcript is checked, else straight to the leaves. -/
theorem mid_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} {o : Word} (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 80 ≤ need)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hO : OpenT env m o) (hC : Ctx env top regs m)
    (hL3 : ∀ R M, L3Inv env ret top regs m o (m.getMem (o + 16#64)).toNat R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 162, ret, top⟩ :: rest, R, M⟩)
    (hD : ∀ R M, DInv env ret top regs m o R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 204, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, L2Inv env ret top regs m o 0 R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 154, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  have hBM := hI.1.2.1
  have hTw := hC.tT.2.1
  rv_introT hI
  rv_symT hp stop [162, 204] with [(by omega : env.stackLimit.toNat + 80 ≤ top.toNat)]
  · exact hD _ _ ⟨base_regs hBM, by rv_closeT, by simp only [Tactic.rf]; exact hI_25⟩
  · refine hL3 _ _ ⟨base_regs hBM, by rv_closeT, by rv_closeT, ?_, ?_, Nat.le_refl _⟩
    · simp only [Tactic.rf, Nat.sub_self, Nat.mul_zero]; exact (BitVec.add_zero _).symm
    · simp only [Tactic.rf]; exact shl56 hO.b56

/-- The fourth loop's head (instruction 274), `j` leaves copied of the `n` paths at `P` into the buffer `buf`
    allocated since the entry: each copied slice the path's leaf. -/
def L4Inv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (o : Word) (k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  Base env ret top regs m R M ∧ R .x13 = m.getMem (o + 16#64) ∧ R .x15 = m.getMem (o + 16#64) ∧
    1 ≤ k ∧ k ≤ (m.getMem (o + 16#64)).toNat ∧
    (env.next m).toNat ≤ (R .x12).toNat ∧ (R .x12).toNat + 16 * (m.getMem (o + 16#64)).toNat ≤ (env.next M).toNat ∧
    (R .x12).toNat % 8 = 0 ∧
    (R .x8).toNat = (R .x12).toNat + 8 + 16 * (m.getMem (o + 16#64)).toNat ∧
    R .x14 = R .x12 + BitVec.ofNat 64 (8 + 16 * ((m.getMem (o + 16#64)).toNat - k)) ∧
    R .x11 = m.getMem (o + 8#64) + BitVec.ofNat 64 (16 + 56 * ((m.getMem (o + 16#64)).toNat - k)) ∧
    ∀ j < (m.getMem (o + 16#64)).toNat - k,
      M.getMem (R .x12 + BitVec.ofNat 64 (16 * j)) = m.getMem (m.getMem (o + 8#64) + BitVec.ofNat 64 (56 * j + 8)) ∧
      M.getMem (R .x12 + BitVec.ofNat 64 (16 * j + 8)) = m.getMem (m.getMem (o + 8#64) + BitVec.ofNat 64 (56 * j + 16))

/-- The exit's stores (instruction 288): the vector's capacity, pointer and length in `x13`, `x12`, `x15`, its buffer
    `BufT`, each slice `SliceKT`. -/
def FInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  Base env ret top regs m R M ∧ BufT env M (R .x13) (R .x12) 16 ∧ (R .x13).toNat * 16 < 2 ^ 63 ∧
    (R .x15).toNat ≤ (R .x13).toNat ∧ ((R .x15).toNat = 0 ∨ (env.next m).toNat ≤ (R .x12).toNat) ∧
    ∀ j < (R .x15).toNat, SliceKT env M (R .x12 + BitVec.ofNat 64 (16 * j))

/-- The capacity's check passed: `16 n` without overflow, at most `isize::MAX` rounded to 8. -/
theorem cap_ok {x : Word}
    (h : BinOp.ult.eval 0#64 (x >>> 60) ||| BinOp.ult.eval 9223372036854775800#64 (x <<< 4) = 0#64) :
    (x <<< 4).toNat = 16 * x.toNat ∧ 16 * x.toNat ≤ 9223372036854775800 := by
  simp only [BinOp.eval] at h
  have hx := x.isLt
  by_cases h1 : BitVec.ult 0#64 (x >>> 60) <;> by_cases h2 : BitVec.ult 9223372036854775800#64 (x <<< 4) <;>
    simp only [h1, h2, ite_true, ite_false, Bool.false_eq_true] at h
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · simp only [BitVec.ult, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
      Nat.shiftLeft_eq, decide_eq_true_eq, BitVec.toNat_ofNat, Nat.not_lt] at h1 h2 ⊢
    omega

set_option rv_sym.heap true in
/-- The leaves' collection: the capacity's check, `alloc`, on to the copy or the exit. -/
theorem coll_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needA needH : Nat} (hnA : 80 + needA ≤ need) (hnH : 80 + needH ≤ need)
    (hac : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA) (hhe : Aborts env p L.handleError.idx needH)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} {o : Word} (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hO : OpenT env m o)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hL4 : ∀ R M, L4Inv env ret top regs m o (m.getMem (o + 16#64)).toNat R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 274, ret, top⟩ :: rest, R, M⟩)
    (hF : ∀ R M, FInv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 288, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, DInv env ret top regs m o R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 204, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  have hBM := hI.1.2.1
  rv_introT hI
  have hnM := hBM.1.1
  have hb56 := hO.b56
  rv_symT hp stop [274, 288] with [hL, (by omega : env.stackLimit.toNat + 80 ≤ top.toNat)] using [hac, hhe]
  -- no paths: the empty vector
  · refine hF _ _ ⟨base_regs hBM, Or.inl rfl, by simp only [Tactic.rf]; simp, by simp only [Tactic.rf]; simp [hc],
      Or.inl (by simp only [Tactic.rf]; simp [hc]), fun j hj => absurd hj (by simp only [Tactic.rf]; simp [hc])⟩
  · exact absurd (cap_ok hc_1).1 (by rw [hc_2]; have := (BitVec.toNat_ne_iff_ne).2 hc; simp at this ⊢; omega)
  · have := (cap_ok hc_1).2; rw [(cap_ok hc_1).1]; omega
  · exact absurd (by rw [hc]; rfl) hc_2
  -- the buffer allocated: on to the copy
  · obtain ⟨e16, hle⟩ := cap_ok hc_1
    have hB1 := baseM_call hBM (by omega) hret1_14 (fun b h => h.elim) hret1_19 hret1_15
    have hn1 : 1 ≤ (m.getMem (o + 16#64)).toNat := Nat.pos_of_ne_zero fun h => hc (BitVec.eq_of_toNat_eq h)
    have hnx1 := hret1_14.2.1
    rw [e16] at hret1_18
    refine hL4 _ _ ⟨base_regs hB1, by rv_closeT, by rv_closeT, hn1, Nat.le_refl _, ?_, ?_, ?_, ?_, ?_, ?_,
      fun j hj => absurd hj (by omega)⟩
    · simp only [Tactic.rf]; omega
    · simp only [Tactic.rf]; omega
    · simp only [Tactic.rf]; exact hret1_17
    · have := hW.heapEnd_le
      simp only [Tactic.rf]; rw [BitVec.toNat_add, BitVec.toNat_add, e16]; simp; omega
    · simp only [Tactic.rf, Nat.sub_self, Nat.mul_zero, Nat.add_zero]
    · simp only [Tactic.rf, Nat.sub_self, Nat.mul_zero, Nat.add_zero]

/-- The copy's step: the slice `(v1, v2)` stored at element `j` of the buffer keeps the earlier elements. -/
theorem copy_step {M : MachineState} {buf : Word} {j : Nat} {A B : Nat → Word} {v1 v2 : Word}
    (hb : buf.toNat + 16 * (j + 1) < 2 ^ 64)
    (hIH : ∀ j' < j, M.getMem (buf + BitVec.ofNat 64 (16 * j')) = A j' ∧
      M.getMem (buf + BitVec.ofNat 64 (16 * j' + 8)) = B j') (h1 : v1 = A j) (h2 : v2 = B j) :
    ∀ j' < j + 1,
      ((M.setMem (buf + BitVec.ofNat 64 (8 + 16 * j) + 18446744073709551608#64) v1).setMem
          (buf + BitVec.ofNat 64 (8 + 16 * j)) v2).getMem (buf + BitVec.ofNat 64 (16 * j')) = A j' ∧
      ((M.setMem (buf + BitVec.ofNat 64 (8 + 16 * j) + 18446744073709551608#64) v1).setMem
          (buf + BitVec.ofNat 64 (8 + 16 * j)) v2).getMem (buf + BitVec.ofNat 64 (16 * j' + 8)) = B j' := by
  intro j' hj'
  have e2 : (buf + BitVec.ofNat 64 (8 + 16 * j)).toNat = buf.toNat + 8 + 16 * j := by
    rw [toNat_add_ofNat (by omega)]; omega
  have e1 : (buf + BitVec.ofNat 64 (8 + 16 * j) + 18446744073709551608#64).toNat = buf.toNat + 16 * j := by
    rw [BitVec.toNat_add, e2]; simp; omega
  have f1 : (buf + BitVec.ofNat 64 (16 * j')).toNat = buf.toNat + 16 * j' := toNat_add_ofNat (by omega)
  have f2 : (buf + BitVec.ofNat 64 (16 * j' + 8)).toNat = buf.toNat + 16 * j' + 8 := by
    rw [toNat_add_ofNat (by omega)]; omega
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with h | rfl
  · rw [MachineState.getMem_setMem_ne (ne_of_toNat_lt (by rw [f1, e2]; omega)),
      MachineState.getMem_setMem_ne (ne_of_toNat_lt (by rw [f1, e1]; omega)),
      MachineState.getMem_setMem_ne (ne_of_toNat_lt (by rw [f2, e2]; omega)),
      MachineState.getMem_setMem_ne (ne_of_toNat_lt (by rw [f2, e1]; omega))]
    exact hIH j' h
  · have g1 : buf + BitVec.ofNat 64 (16 * j') = buf + BitVec.ofNat 64 (8 + 16 * j') + 18446744073709551608#64 :=
      BitVec.eq_of_toNat_eq (by rw [f1, e1])
    have g2 : buf + BitVec.ofNat 64 (16 * j' + 8) = buf + BitVec.ofNat 64 (8 + 16 * j') :=
      BitVec.eq_of_toNat_eq (by rw [f2, e2]; omega)
    rw [g1, MachineState.getMem_setMem_ne (ne_of_toNat_lt (by rw [e1, e2]; omega)), MachineState.getMem_setMem_eq,
      g2, MachineState.getMem_setMem_eq]
    exact ⟨h1, h2⟩

/-- A slice read at `s` in `M` as at `a` in `m`, `NEXT` not lower, keeps `SliceKT`. -/
theorem sliceKT_of {env : Env} {m M : MachineState} {s a : Word} (h : SliceKT env m a)
    (h0 : M.getMem s = m.getMem a) (h8 : M.getMem (s + 8#64) = m.getMem (a + 8#64))
    (hn : (env.next m).toNat ≤ (env.next M).toNat) : SliceKT env M s := by
  unfold SliceKT at h ⊢
  unfold Env.Live at h ⊢
  rw [h0, h8]
  exact h.imp id fun ⟨h1, h2, h3⟩ => ⟨by omega, h2, h3⟩

/-- The copied slices are the paths' leaves, so `SliceKT`. -/
theorem slices_of {env : Env} {m M : MachineState} {buf P : Word} {n : Nat}
    (hP : ∀ j < n, PathT env m (P + BitVec.ofNat 64 (56 * j)))
    (hc : ∀ j < n, M.getMem (buf + BitVec.ofNat 64 (16 * j)) = m.getMem (P + BitVec.ofNat 64 (56 * j + 8)) ∧
      M.getMem (buf + BitVec.ofNat 64 (16 * j + 8)) = m.getMem (P + BitVec.ofNat 64 (56 * j + 16)))
    (hn : (env.next m).toNat ≤ (env.next M).toNat) :
    ∀ j < n, SliceKT env M (buf + BitVec.ofNat 64 (16 * j)) := by
  intro j hj
  refine sliceKT_of (hP j hj).1 ?_ ?_ hn
  · rw [(hc j hj).1, add_ofNat_add]
  · rw [add_ofNat_add, (hc j hj).2, add_ofNat_add, add_ofNat_add]

/-- Two stores into the buffer, below `NEXT` and so apart from the stack, keep `BaseM`. -/
theorem baseM_fresh2 {env : Env} {ret top : Word} {regs : Reg → Word} {m M : MachineState} {a1 a2 v1 v2 : Word}
    (hB : BaseM env ret top regs m M) (hW : Windows env top m) (hlim : env.stackLimit.toNat ≤ top.toNat)
    (h1 : (env.next m).toNat ≤ a1.toNat) (h1' : a1.toNat < (env.next M).toNat)
    (h2 : (env.next m).toNat ≤ a2.toNat) (h2' : a2.toNat < (env.next M).toNat) :
    BaseM env ret top regs m ((M.setMem a1 v1).setMem a2 v2) := by
  have := env.layout
  have := hW.heapEnd_le
  have := hW.nextAddr_ge
  have hnx := hB.1.2.1
  have n1 : a1 ≠ env.nextAddr := ne_of_toNat_lt (Or.inl (by omega))
  have n2 : a2 ≠ env.nextAddr := ne_of_toNat_lt (Or.inl (by omega))
  have e1 : env.next (M.setMem a1 v1) = env.next M := Tactic.next_setMem n1
  obtain ⟨hF, hc, hs, s1, s2, s3, s4, s5, s6⟩ := hB
  have hk : ∀ c : Nat, 0 < c → c ≤ 48 → ((M.setMem a1 v1).setMem a2 v2).getMem (top + BitVec.ofNat 64 (2 ^ 64 - c)) =
      M.getMem (top + BitVec.ofNat 64 (2 ^ 64 - c)) := fun c hc0 hc1 => by
    have e : (top + BitVec.ofNat 64 (2 ^ 64 - c)).toNat = top.toNat - c := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [MachineState.getMem_setMem_ne (ne_of_toNat_lt (by rw [e]; omega)),
      MachineState.getMem_setMem_ne (ne_of_toNat_lt (by rw [e]; omega))]
  refine ⟨Tactic.frame_fresh (Tactic.frame_fresh hF rfl h1 h1') e1 h2 h2',
    by rw [MachineState.code_setMem, MachineState.code_setMem]; exact hc,
    Tactic.static_store (Tactic.static_store hs (Or.inl (by omega))) (Or.inl (by omega)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (18446744073709551608#64 : Word) = BitVec.ofNat 64 (2 ^ 64 - 8) from rfl, hk 8 (by omega) (by omega)]
    exact s1
  · rw [show (18446744073709551600#64 : Word) = BitVec.ofNat 64 (2 ^ 64 - 16) from rfl,
      hk 16 (by omega) (by omega)]
    exact s2
  · rw [show (18446744073709551592#64 : Word) = BitVec.ofNat 64 (2 ^ 64 - 24) from rfl,
      hk 24 (by omega) (by omega)]
    exact s3
  · rw [show (18446744073709551584#64 : Word) = BitVec.ofNat 64 (2 ^ 64 - 32) from rfl,
      hk 32 (by omega) (by omega)]
    exact s4
  · rw [show (18446744073709551576#64 : Word) = BitVec.ofNat 64 (2 ^ 64 - 40) from rfl,
      hk 40 (by omega) (by omega)]
    exact s5
  · rw [show (18446744073709551568#64 : Word) = BitVec.ofNat 64 (2 ^ 64 - 48) from rfl,
      hk 48 (by omega) (by omega)]
    exact s6

set_option rv_sym.heap true in
/-- From the exit: `Ok` of the vector into the slot, the return. -/
theorem fin_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostK env) Merkle.Out ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 80 ≤ need) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hC : Ctx env top regs m) :
    ∀ R M, FInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 288, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  have hF := frame_widen hinv.1.2.1.1 offOut_out
  obtain ⟨-, hbuf, hcap, hlen, hfr, hsl⟩ := id hinv
  rv_introT hinv
  have hwS := hC.wS
  have haS := hC.aS
  have hoS := hC.oS
  rv_symT hp with [(by omega : env.stackLimit.toNat + 80 ≤ top.toNat)]
  rv_symT hp with [(by omega : env.stackLimit.toNat + 80 ≤ top.toNat)]
  all_goals
    have hlS := hwS.lt
    have hlay := env.layout
    have := hW.heapEnd_le
    have := hW.nextAddr_ge
    have e8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
    have e16 : (regs .x10 + 16#64).toNat = (regs .x10).toNat + 16 := toNat_add_ofNat (by omega)
  · have o0 : Merkle.Out regs m (regs .x10) := Or.inl ⟨Nat.le_refl _, by simp only [Layouts.ResultVecE.byteSize]; omega⟩
    have o8 : Merkle.Out regs m (regs .x10 + 8#64) := Or.inl (by
      simp only [InRange, Layouts.ResultVecE.byteSize]; rw [e8]; omega)
    have o16 : Merkle.Out regs m (regs .x10 + 16#64) := Or.inl (by
      simp only [InRange, Layouts.ResultVecE.byteSize]; rw [e16]; omega)
    exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out hF o0 (hwS.ne_next (Nat.le_refl _) (by omega)))
      o8 (hwS.ne_next_add (o := 8) (by omega))) o16 (hwS.ne_next_add (o := 16) (by omega))
  · intro _
    refine ⟨vecT_stores hwS haS hbuf hcap hlen, fun k hk => ?_⟩
    have hfr' := hfr.resolve_left (by omega)
    obtain ⟨-, hbl, -⟩ := hbuf.resolve_left (by omega)
    unfold Env.Live at hbl
    have hnM := hF.2.1
    have hoS' := hoS
    unfold Env.Owned at hoS'
    have es : (R .x12 + BitVec.ofNat 64 (16 * k)).toNat = (R .x12).toNat + 16 * k := toNat_add_ofNat (by omega)
    have es8 : (R .x12 + BitVec.ofNat 64 (16 * k) + 8#64).toNat = (R .x12).toNat + 16 * k + 8 := by
      rw [toNat_add_ofNat (by omega), es]
    have hn : env.next (((M.setMem (regs .x10) (R .x13)).setMem (regs .x10 + 8#64) (R .x12)).setMem
        (regs .x10 + 16#64) (R .x15)) = env.next M := by
      rw [Tactic.next_setMem (hwS.ne_next_add (o := 16) (by omega)),
        Tactic.next_setMem (hwS.ne_next_add (o := 8) (by omega)), Tactic.next_setMem (hwS.ne_next (Nat.le_refl _)
        (by omega))]
    refine sliceKT_of (hsl k hk) ?_ ?_ (by rw [hn])
    · rw [MachineState.getMem_setMem_ne (ne_of_toNat_lt (by rw [e16, es]; omega)),
        MachineState.getMem_setMem_ne (ne_of_toNat_lt (by rw [e8, es]; omega)),
        MachineState.getMem_setMem_ne (ne_of_toNat_lt (by rw [es]; omega))]
    · rw [MachineState.getMem_setMem_ne (ne_of_toNat_lt (by rw [e16, es8]; omega)),
        MachineState.getMem_setMem_ne (ne_of_toNat_lt (by rw [e8, es8]; omega)),
        MachineState.getMem_setMem_ne (ne_of_toNat_lt (by rw [es8]; omega))]

set_option rv_sym.heap true in
/-- **The leaves' copy**: each path's leaf slice into the buffer, then the exit. -/
theorem loop4 (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} {o : Word} (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 80 ≤ need)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hO : OpenT env m o) (hC : Ctx env top regs m)
    (hF : ∀ R M, FInv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 288, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, L4Inv env ret top regs m o k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 274, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (L4Inv env ret top regs m o) fun k R M hI ih => ?_
  have hBM := hI.1.2.1
  have hTl := hC.tT.2.1.lt
  have hTs := hC.tS
  have := hW.heapEnd_le
  have := hW.next_ge
  have := hW.nextAddr_ge
  have := env.layout
  obtain ⟨-, -, -, hk1, hkn, hfr, hfr2, hba, -, -, -, hcp⟩ := id hI
  obtain ⟨hPa, hPl, hPw', hPs⟩ := hO.ps.resolve_left (by omega)
  unfold Env.Live at hPl
  have hPlt := hPw'.lt
  have hnM := hBM.1.2.1
  have hbw : InWin env (R .x12) (16 * (m.getMem (o + 16#64)).toNat) := Or.inl ⟨by omega, by omega⟩
  have hx11 : (m.getMem (o + 8#64) + BitVec.ofNat 64 (16 + 56 * ((m.getMem (o + 16#64)).toNat - k))).toNat =
      (m.getMem (o + 8#64)).toNat + 16 + 56 * ((m.getMem (o + 16#64)).toNat - k) := by
    rw [toNat_add_ofNat (by omega)]; omega
  have hx14 : (R .x12 + BitVec.ofNat 64 (8 + 16 * ((m.getMem (o + 16#64)).toNat - k))).toNat =
      (R .x12).toNat + 8 + 16 * ((m.getMem (o + 16#64)).toNat - k) := by
    rw [toNat_add_ofNat (by omega)]; omega
  have w1 := hPw'.dword hW hPa (o := 56 * ((m.getMem (o + 16#64)).toNat - k) + 8)
    (x := m.getMem (o + 8#64) + BitVec.ofNat 64 (16 + 56 * ((m.getMem (o + 16#64)).toNat - k)) +
      18446744073709551608#64) (by rw [BitVec.toNat_add, hx11]; simp; omega) (by omega) (by omega)
  have w2 := hPw'.dword hW hPa (o := 56 * ((m.getMem (o + 16#64)).toNat - k) + 16)
    (x := m.getMem (o + 8#64) + BitVec.ofNat 64 (16 + 56 * ((m.getMem (o + 16#64)).toNat - k)))
    (by rw [hx11]; omega) (by omega) (by omega)
  have w3 := hbw.dword hW hba (o := 16 * ((m.getMem (o + 16#64)).toNat - k))
    (x := R .x12 + BitVec.ofNat 64 (8 + 16 * ((m.getMem (o + 16#64)).toNat - k)) + 18446744073709551608#64)
    (by rw [BitVec.toNat_add, hx14]; simp; omega) (by omega) (by omega)
  have w4 := hbw.dword hW hba (o := 16 * ((m.getMem (o + 16#64)).toNat - k) + 8)
    (x := R .x12 + BitVec.ofNat 64 (8 + 16 * ((m.getMem (o + 16#64)).toNat - k))) (by rw [hx14]; omega)
    (by omega) (by omega)
  rv_introT hI
  rv_symT hp stop [274, 288] with [(by omega : env.stackLimit.toNat + 80 ≤ top.toNat)]
  all_goals
    have ea1 : (R .x12 + BitVec.ofNat 64 (8 + 16 * ((m.getMem (o + 16#64)).toNat - k)) +
        18446744073709551608#64).toNat = (R .x12).toNat + 16 * ((m.getMem (o + 16#64)).toNat - k) := by
      rw [BitVec.toNat_add, hx14]; simp; omega
    have hB2 := baseM_fresh2 (v1 := M.getMem (m.getMem (o + 8#64) +
        BitVec.ofNat 64 (16 + 56 * ((m.getMem (o + 16#64)).toNat - k)) + 18446744073709551608#64))
      (v2 := M.getMem (m.getMem (o + 8#64) + BitVec.ofNat 64 (16 + 56 * ((m.getMem (o + 16#64)).toNat - k))))
      hBM hW (by omega) (by rw [ea1]; omega) (by rw [ea1]; omega) (by rw [hx14]; omega) (by rw [hx14]; omega)
    have hn2 := hB2.1.1
    have hcp2 := copy_step (M := M) (buf := R .x12) (j := (m.getMem (o + 16#64)).toNat - k)
      (A := fun j => m.getMem (m.getMem (o + 8#64) + BitVec.ofNat 64 (56 * j + 8)))
      (B := fun j => m.getMem (m.getMem (o + 8#64) + BitVec.ofNat 64 (56 * j + 16)))
      (v1 := M.getMem (m.getMem (o + 8#64) +
        BitVec.ofNat 64 (16 + 56 * ((m.getMem (o + 16#64)).toNat - k)) + 18446744073709551608#64))
      (v2 := M.getMem (m.getMem (o + 8#64) + BitVec.ofNat 64 (16 + 56 * ((m.getMem (o + 16#64)).toNat - k))))
      (by omega) hcp
      (by
        have e : m.getMem (o + 8#64) + BitVec.ofNat 64 (16 + 56 * ((m.getMem (o + 16#64)).toNat - k)) +
            18446744073709551608#64 =
            m.getMem (o + 8#64) + BitVec.ofNat 64 (56 * ((m.getMem (o + 16#64)).toNat - k) + 8) :=
          BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_add, hx11, toNat_add_ofNat (by omega)]; simp; omega)
        rw [e]
        exact keepLow hBM.1 hnx hTs hTl hW (by omega) (by rw [toNat_add_ofNat (by omega)]; omega))
      (by
        have e : m.getMem (o + 8#64) + BitVec.ofNat 64 (16 + 56 * ((m.getMem (o + 16#64)).toNat - k)) =
            m.getMem (o + 8#64) + BitVec.ofNat 64 (56 * ((m.getMem (o + 16#64)).toNat - k) + 16) :=
          BitVec.eq_of_toNat_eq (by rw [hx11, toNat_add_ofNat (by omega)]; omega)
        rw [e]
        exact keepLow hBM.1 hnx hTs hTl hW (by omega) (by rw [toNat_add_ofNat (by omega)]; omega))
    have hnn : env.next ((M.setMem (R .x12 + BitVec.ofNat 64 (8 + 16 * ((m.getMem (o + 16#64)).toNat - k)) +
        18446744073709551608#64) (M.getMem (m.getMem (o + 8#64) +
        BitVec.ofNat 64 (16 + 56 * ((m.getMem (o + 16#64)).toNat - k)) + 18446744073709551608#64))).setMem
        (R .x12 + BitVec.ofNat 64 (8 + 16 * ((m.getMem (o + 16#64)).toNat - k)))
        (M.getMem (m.getMem (o + 8#64) + BitVec.ofNat 64 (16 + 56 * ((m.getMem (o + 16#64)).toNat - k))))) =
        env.next M := by
      rw [Tactic.next_setMem (ne_of_toNat_lt (Or.inl (by rw [hx14]; omega))),
        Tactic.next_setMem (ne_of_toNat_lt (Or.inl (by rw [ea1]; omega)))]
  -- the next path
  · have hk2 : 2 ≤ k := by
      by_contra h
      apply hc
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, hx14, hI_26]
      simp
      omega
    refine ih (k - 1) _ _ (by omega) ⟨base_regs hB2, by rv_closeT, by rv_closeT, by omega, by omega, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    all_goals simp only [Tactic.rf]
    · exact hI_23
    · rw [hnn]; omega
    · exact hI_25
    · exact hI_26
    · rw [add_ofNat_add, show 8 + 16 * ((m.getMem (o + 16#64)).toNat - k) + 16 =
        8 + 16 * ((m.getMem (o + 16#64)).toNat - (k - 1)) by omega]
    · rw [add_ofNat_add, show 16 + 56 * ((m.getMem (o + 16#64)).toNat - k) + 56 =
        16 + 56 * ((m.getMem (o + 16#64)).toNat - (k - 1)) by omega]
    · intro j hj; exact hcp2 j (by omega)
  -- every leaf copied
  · have hk1' : k = 1 := by
      have := congrArg BitVec.toNat hc
      rw [BitVec.toNat_add, hx14, hI_26] at this
      simp at this
      omega
    subst hk1'
    refine hF _ _ ⟨base_regs hB2, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [Tactic.rf]
    · exact .inr ⟨by omega, by unfold Env.Live; rw [hnn]; omega, hI_25⟩
    · omega
    · exact Nat.le_refl _
    · exact .inr hI_23
    · exact slices_of hPs (fun j hj => hcp2 j (by omega)) hn2

/-- The opening the code addresses, `PO + 24 off`, from the openings' facts. -/
theorem openT_of {env : Env} {m : MachineState} {PO off : Word} {nO : Nat} (hPa : PO.toNat % 8 = 0)
    (hPl : env.Live m PO (24 * nO)) (hPw : InWin env PO (24 * nO))
    (hPs : ∀ k < nO, PathsT env m (PO + BitVec.ofNat 64 (24 * k))) (hoff : off.toNat < nO)
    (hy : (off <<< 4 + off <<< 3).toNat = 24 * off.toNat) : OpenT env m (PO + (off <<< 4 + off <<< 3)) := by
  have hlt := hPw.lt
  have e : off <<< 4 + off <<< 3 = BitVec.ofNat 64 (24 * off.toNat) :=
    BitVec.eq_of_toNat_eq (by rw [hy, BitVec.toNat_ofNat]; omega)
  have e2 : (PO + BitVec.ofNat 64 (24 * off.toNat)).toNat = PO.toNat + 24 * off.toNat := toNat_add_ofNat (by omega)
  unfold Env.Live at hPl
  rw [e]
  exact ⟨hPw.sub (by omega) (by omega), by omega, by unfold Env.Live; omega, hPs _ hoff⟩

set_option rv_sym.heap true in
/-- **`Transcript::merkle` returns `PostK`**: the entry, the shape's, positions' and roots' checks, the leaves'
    collection and copy, each error. -/
theorem kept (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hdata : DataRef.InData env (tables L)) {need needR needC needA needH : Nat} (hnR : 80 + needR ≤ need)
    (hnC : 80 + needC ≤ need) (hnA : 80 + needA ≤ need) (hnH : 80 + needH ≤ need)
    (hro : Merkle.RootT.specT env p L.root.idx needR) (hmc : Runtime.MemcmpT.MemcmpSpecT env p L.memcmp.idx needC)
    (hac : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA) (hhe : Aborts env p L.handleError.idx needH) :
    HoldsT env p i need (PreT env) (PostK env) Merkle.Out (Stop := AbortStop) := by
  rv_autoT hp stop [2] with [hL, (by omega : env.stackLimit.toNat + 80 ≤ top.toNat)]
  have hC : Ctx env top regs m := hpre_2 ▸ ⟨⟨⟨hpre_6, hpre_7, hpre_8, hpre_9⟩, hpre_10, hpre_11, hpre_12, hpre_13, hpre_14⟩,
    ⟨⟨hpre_15, hpre_16⟩, ⟨hpre_17, hpre_18⟩⟩, hpre_19, hpre_20, hpre_21, hpre_22, ⟨hpre_23, hpre_24⟩, hpre_25, hpre_26,
    hpre_27, hpre_28⟩
  clear hpre_7 hpre_8 hpre_9 hpre_11 hpre_14 hpre_20 hpre_21 hpre_22 hpre_23 hpre_24 hpre_25 hpre_26 hpre_27
    hpre_28
  obtain ⟨hca, hcw, -⟩ : _ ∧ inWindow (L.d_c8_14ca7de5.hi + L.d_c8_14ca7de5.lo) 8 = true ∧ _ :=
    Hash.KeccakFT.table_range (ws := Gen.Verifier.Transcript.Transcript.Merkle.d_c8_14ca7de5_words)
    hpre_30 hpre_4 (hdata _ (List.mem_cons_self ..)) (by decide) (by decide)
  obtain ⟨-, hbw, -⟩ : _ ∧ inWindow (L.d_c64_b1d69b10.hi + L.d_c64_b1d69b10.lo) 64 = true ∧ _ :=
    Hash.KeccakFT.table_range
    (ws := Gen.Verifier.Transcript.Transcript.Merkle.d_c64_b1d69b10_words) hpre_30 hpre_4
    (hdata _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (by decide) (by decide)
  have hT := hC.tT
  have hTw := hT.2.1
  have hQ := hT.2.2.2
  have herr := err_ok env p i L hp hk hpre_3 (by omega) hpre_5 hpre_29 hpre_30 hC
  rv_symT hp stop [32, 132] with [hL, (by omega : env.stackLimit.toNat + 80 ≤ top.toNat)]
  · exact herr _ _ ⟨⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT,
      by rv_closeT⟩, ⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT,
      by rv_closeT, by rv_closeT⟩, by rv_closeT⟩
  · have hoff := BitVec.lt_def.1 hc
    rcases hC.oP with h0 | ⟨hPa, hPl, hPw, hPs⟩
    · exact absurd hoff (by omega)
    have hPlt := hPw.lt
    have hy := shl24 (x := m.getMem (regs .x11 + 344#64)) (by omega)
    have hxo : (m.getMem (m.getMem (regs .x11 + 328#64) + 32#64) + (m.getMem (regs .x11 + 344#64) <<< 4 +
        m.getMem (regs .x11 + 344#64) <<< 3)).toNat = (m.getMem (m.getMem (regs .x11 + 328#64) + 32#64)).toNat +
        24 * (m.getMem (regs .x11 + 344#64)).toNat := by
      rw [BitVec.toNat_add, hy]; omega
    clear hc
    have hO := openT_of hPa hPl hPw hPs hoff hy
    rv_symT hp stop [82, 132] with [hL, (by omega : env.stackLimit.toNat + 80 ≤ top.toNat)]
    · exact hcw
    · exact byte_in hbw _
    have hfin := fin_ok env p i L hp hk hpre_3 (by omega) hpre_5 hpre_29 hpre_30 hC
    have h4 := loop4 env p i L hp hpre_3 (by omega) hpre_5 hpre_29 hpre_30 hO hC hfin
    have hD := coll_ok env p i L hp hL hnA hnH hac hhe hpre_3 hpre_29 hpre_30 hO hstop (h4 _) hfin
    have h3 := loop3 env p i L hp hL hnR hnC hro hmc hpre_3 hpre_5 hpre_29 hpre_30 hO hC hstop herr hD
    have hM := mid_ok env p i L hp hpre_3 (by omega) hpre_29 hpre_30 hO hC (h3 _) hD
    have h2 := loop2 env p i L hp hpre_3 (by omega) hpre_29 hpre_30 hO hC.wQ herr hM
    · refine loop1 env p i L hp hpre_3 (by omega) hpre_30 hO herr (h2 _) _ _ _
        ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, Nat.le_refl _⟩
      all_goals try rv_closeT
      · exact Tactic.frame_out (by rv_closeT) rfl (hTw.ne_next_add (o := 344) (by decide))
      · exact shl56 hO.b56
      · simp only [Nat.sub_self, Nat.mul_zero]; exact (BitVec.add_zero _).symm
  · exact herr _ _ ⟨⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT,
      by rv_closeT⟩, ⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT,
      by rv_closeT, by rv_closeT⟩, by rv_closeT⟩

/-- `Merkle.Out` misses the transcript's words `TranscriptAtT` reads and its proof's stream words: the slot apart from
    both, the opening offset another word. -/
theorem out_miss {env : Env} {regs : Reg → Word} {m : MachineState} (h : PreT env regs m) :
    (∀ k, (k = 0 ∨ k = 320 ∨ k = 328) → ¬ Merkle.Out regs m (regs .x11 + BitVec.ofNat 64 k)) ∧
      ∀ k, (k = 8 ∨ k = 16) → ¬ Merkle.Out regs m (m.getMem (regs .x11 + 328#64) + BitVec.ofNat 64 k) := by
  obtain ⟨⟨_, hT, hA, _, hQ, _⟩, _, _, _, hW, _, _, hR, hP, _, _⟩ := h
  have ha := hT.lt
  have hq := hQ.lt
  have hw := hW.lt
  unfold Apart at hA hR hP
  simp only [Layouts.Transcript.byteSize, Layouts.Proof.byteSize, Layouts.ResultVecE.byteSize] at *
  have h344 : (regs .x11 + 344#64).toNat = (regs .x11).toNat + 344 := toNat_add_ofNat (by omega)
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩ <;> simp only [Merkle.Out, InRange, Layouts.ResultVecE.byteSize, not_or] <;>
    refine ⟨?_, fun he => ?_⟩
  · rw [toNat_add_ofNat (by omega)]; omega
  · have := congrArg BitVec.toNat he
    rw [toNat_add_ofNat (by omega), h344] at this; omega
  · rw [toNat_add_ofNat (by omega)]; omega
  · have := congrArg BitVec.toNat he
    rw [toNat_add_ofNat (by omega), h344] at this; omega

/-- **`Transcript::merkle` is total**, from `kept` and `Merkle.Out`'s frame (`TranscriptAtT.frame`). -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hdata : DataRef.InData env (tables L)) {need needR needC needA needH : Nat} (hnR : 80 + needR ≤ need)
    (hnC : 80 + needC ≤ need) (hnA : 80 + needA ≤ need) (hnH : 80 + needH ≤ need)
    (hro : Merkle.RootT.specT env p L.root.idx needR) (hmc : Runtime.MemcmpT.MemcmpSpecT env p L.memcmp.idx needC)
    (hac : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA) (hhe : Aborts env p L.handleError.idx needH) :
    specT env p i need :=
  Isa.TContract.mono (kept env p i L hp hL hdata hnR hnC hnA hnH hro hmc hac hhe) (fun _ _ _ _ h => h)
    (fun _ top regs m _ _ ⟨⟨he, hs, _, hn, hP, _⟩, _⟩ ⟨⟨ha, hf, hst', hV⟩, hc⟩ => by
      have hT := hP.1.frame (he.2 ▸ hP.2.1) hf hn (by omega) (out_miss hP).1 (out_miss hP).2
      exact ⟨⟨ha, hf, hst', hT.1, he.2 ▸ hT.2.1, hT.2.2, hV⟩, hc⟩)
    fun _ _ _ _ _ _ _ h => h

end Rv64mc.Proof.Transcript.MerkleT

/-- info: 'Rv64mc.Proof.Transcript.MerkleT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Transcript.MerkleT.total
