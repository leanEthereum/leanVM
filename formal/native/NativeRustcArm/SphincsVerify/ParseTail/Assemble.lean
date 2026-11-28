module

public import NativeRustcArm.SphincsVerify.ParseTail.Layer2

/-!
# The parse's tail: the parsed signature assembled at `484` (`b31 .. b35`)

`b31` stores the randomizer at `5124` and copies the FORS openings to `484` (X26 `4640`, X22
`4224`); `b32` stores the first layer's address at `408` and copies layer 0's chain values to
`5140`; `b33`, `b34` store layers 0 and 1's counters (byte-reversed) and copy layers 1 and 2's
chain values; `b35` stores layer 2's counter and the paths' address at `392` and copies the 416
bytes of paths to `4708`.
-/

namespace NativeRustcArm.SphincsVerifyProof.ParseTail

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify
  LeanVM.Protocol.KeccakHash

set_option Elab.async false

@[expose] public section

/-- Layer `l`'s counter as stored: the big-endian bytes of its loaded word reversed. -/
def ctrBytes (r : Run) (l : Nat) : List UInt8 := be32 (UInt32.ofNat (ctr r l).toNat)

/-- The FORS openings in rustc's layout. -/
def forsMem (r : Run) : List UInt8 := (r.sig.fors.map openingMem).flatten

/-- The facts from `b32`. -/
def L32 (r : Run) : List (Nat × Nat × List UInt8) :=
  (484, 4224, forsMem r) :: (5124, 16, r.sig.randomizer) :: L31 r

/-- The registers from `b32`. -/
def K32 (r : Run) : List (XReg × BitVec 64) :=
  (.X26, BitVec.ofNat 64 4640) :: (.X22, BitVec.ofNat 64 4224) :: (.X19, r.off 16960) ::
    (.X23, rev32 (ctr r 2)) :: (.X24, rev32 (ctr r 1)) :: (.X28, rev32 (ctr r 0)) ::
    (.X25, r.off 484) :: [(.X20, r.off 448), (.X21, r.msgPtr)]

/-- The facts from `b35`. -/
def L35 (r : Run) : List (Nat × Nat × List UInt8) :=
  (7196, 1024, wotsRaw r 2) :: (7192, 4, ctrBytes r 1) :: (6168, 1024, wotsRaw r 1) ::
    (6164, 4, ctrBytes r 0) :: (5140, 1024, wotsRaw r 0) ::
    (408, 8, wordBytes (r.addr 5140)) :: L32 r

/-- The paths: layers 0, 1, 2's. -/
def pathsRaw (r : Run) : List UInt8 := (pathRaw r 0 ++ pathRaw r 1) ++ pathRaw r 2

/-- The facts at `b36`. -/
def L36 (r : Run) : List (Nat × Nat × List UInt8) :=
  (4708, 416, pathsRaw r) :: (392, 8, wordBytes (r.addr 4708)) :: (8220, 4, ctrBytes r 2) ::
    (8224, 128 + 128 + 160, pathsRaw r) :: (8224, 128 + 128, pathRaw r 0 ++ pathRaw r 1) ::
    L35 r

end

public section

variable (r : Run) [NativeRustcArm.Host] (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees)
  (hpre : r.Pre)
include hp hc hpre

/-- `b31`: the randomizer to `5124`, the FORS openings to `484`. -/
theorem s31 : Seg r b31Offset (fun m ↦ Facts r m (L31 r) (K28 r)) b32Offset
    (fun m ↦ Facts r m (L32 r) (K32 r)) := fun m h ↦
  step_memcpy r hp hc hpre b31_in_code run_b31 rfl rfl rfl
    (a := 484) (b := 8640) (n := 4224) rfl rfl rfl (by decide) (by decide) (by decide)
    (h.weakenK (K' := (.X19, r.off 16960) :: (.X23, rev32 (ctr r 2)) :: (.X24, rev32 (ctr r 1)) ::
      (.X28, rev32 (ctr r 0)) :: (.X25, r.off 484) :: [(.X20, r.off 448), (.X21, r.msgPtr)])
      (by simp [K28]))
    ⟨(h.reg (x := .X22) (v := r.off 484) (by simp [K28])).trans (ptr_eval r m _ 484).symm, trivial⟩
    (by simp only [L31, L24, L16]; facts_side) (by facts_side)
    (Lnew := [(5124, 16, r.sig.randomizer)])
    (fun _ hm' ↦ copyL r h (o' := 20048) (by simp [L31, L24, L16, baseL]) hm' (by decide)
      (by decide +kernel))
    (Knew := [(.X26, BitVec.ofNat 64 4640), (.X22, BitVec.ofNat 64 4224)])
    (fun _ hm' ↦ ⟨reg_lit r hm' rfl, reg_lit r hm' rfl, trivial⟩)
    (by simp only [L31, L24, L16]; facts_side) (by facts_side) (bs := forsMem r)
    (by simp [L31, L24, L16, baseL, forsMem])

/-- `b32`: the first layer's address at `408`, layer 0's chain values to `5140`. -/
theorem s32 : Seg r b32Offset (fun m ↦ Facts r m (L32 r) (K32 r)) b33Offset
    (fun m ↦ Facts r m ((5140, 1024, wotsRaw r 0) :: (408, 8, wordBytes (r.addr 5140)) ::
      L32 r) (K32 r)) := fun m h ↦
  step_memcpy r hp hc hpre b32_in_code run_b32 rfl rfl rfl
    (a := 5140) (b := 13888) (n := 1024) rfl rfl rfl (by decide) (by decide) (by decide) h
    ⟨(h.reg (x := .X25) (v := r.off 484) (by simp [K32])).trans (ptr_eval r m _ 484).symm, trivial⟩
    (by simp only [L32, L31, L24, L16]; facts_side) (by simp only [K32]; facts_side)
    (Lnew := [(408, 8, wordBytes (r.addr 5140))])
    (fun _ hm' ↦ storeL r hm' (by decide) (by decide))
    (Knew := []) (fun _ _ ↦ trivial)
    (by simp only [L32, L31, L24, L16]; facts_side) (by simp only [K32]; facts_side)
    (bs := wotsRaw r 0) (by simp [L32, L31, L24, L16])

/-- `b33`: layer 0's counter at `6164`, layer 1's chain values to `6168`. -/
theorem s33 : Seg r b33Offset (fun m ↦ Facts r m ((5140, 1024, wotsRaw r 0) ::
      (408, 8, wordBytes (r.addr 5140)) :: L32 r) (K32 r)) b34Offset
    (fun m ↦ Facts r m ((6168, 1024, wotsRaw r 1) :: (6164, 4, ctrBytes r 0) ::
      (5140, 1024, wotsRaw r 0) :: (408, 8, wordBytes (r.addr 5140)) :: L32 r) (K32 r)) :=
  fun m h ↦ step_memcpy r hp hc hpre b33_in_code run_b33 rfl rfl rfl
    (a := 6168) (b := 12864) (n := 1024) rfl rfl rfl (by decide) (by decide) (by decide) h
    ⟨(h.reg (x := .X25) (v := r.off 484) (by simp [K32])).trans (ptr_eval r m _ 484).symm, trivial⟩
    (by simp only [L32, L31, L24, L16]; facts_side) (by simp only [K32]; facts_side)
    (Lnew := [(6164, 4, ctrBytes r 0)])
    (fun _ hm' ↦ store4L r hm' (x := .X28) (v := ctr r 0)
      (h.reg (x := .X28) (v := rev32 (ctr r 0)) (by simp [K32])) (by decide) (by decide))
    (Knew := []) (fun _ _ ↦ trivial)
    (by simp only [L32, L31, L24, L16]; facts_side) (by simp only [K32]; facts_side)
    (bs := wotsRaw r 1) (by simp [L32, L31, L24])

/-- `b34`: layer 1's counter at `7192`, layer 2's chain values to `7196`. -/
theorem s34 : Seg r b34Offset (fun m ↦ Facts r m ((6168, 1024, wotsRaw r 1) ::
      (6164, 4, ctrBytes r 0) :: (5140, 1024, wotsRaw r 0) ::
      (408, 8, wordBytes (r.addr 5140)) :: L32 r) (K32 r)) b35Offset
    (fun m ↦ Facts r m (L35 r) (K32 r)) :=
  fun m h ↦ step_memcpy r hp hc hpre b34_in_code run_b34 rfl rfl rfl
    (a := 7196) (b := 17984) (n := 1024) rfl rfl rfl (by decide) (by decide) (by decide) h
    ⟨(h.reg (x := .X25) (v := r.off 484) (by simp [K32])).trans (ptr_eval r m _ 484).symm, trivial⟩
    (by simp only [L32, L31, L24, L16]; facts_side) (by simp only [K32]; facts_side)
    (Lnew := [(7192, 4, ctrBytes r 1)])
    (fun _ hm' ↦ store4L r hm' (x := .X24) (v := ctr r 1)
      (h.reg (x := .X24) (v := rev32 (ctr r 1)) (by simp [K32])) (by decide) (by decide))
    (Knew := []) (fun _ _ ↦ trivial)
    (by simp only [L32, L31, L24, L16]; facts_side) (by simp only [K32]; facts_side)
    (bs := wotsRaw r 2) (by simp [L32, L31])

/-- `b35`: layer 2's counter at `8220`, the paths' address at `392`, the paths to `4708`. -/
theorem s35 : Seg r b35Offset (fun m ↦ Facts r m (L35 r) (K32 r)) b36Offset
    (fun m ↦ Facts r m (L36 r) (K32 r)) := fun m h ↦
  step_memcpy r hp hc hpre b35_in_code run_b35 rfl rfl rfl
    (a := 4708) (b := 8224) (n := 416) rfl rfl rfl (by decide) (by decide) (by decide)
    ((h.concat (o := 8224) (n := 128) (n' := 128) (xs := pathRaw r 0) (ys := pathRaw r 1)
      (by simp [L35, L32, L31, L24, L16]) (by simp [L35, L32, L31, L24])).concat
      (o := 8224) (n := 128 + 128) (n' := 160) (xs := pathRaw r 0 ++ pathRaw r 1)
      (ys := pathRaw r 2) List.mem_cons_self (by simp [L35, L32, L31]))
    ⟨(h.reg (x := .X25) (v := r.off 484) (by simp [K32])).trans (ptr_eval r m _ 484).symm,
      h.reg (x := .X22) (v := BitVec.ofNat 64 4224) (by simp [K32]), trivial⟩
    (by simp only [L35, L32, L31, L24, L16]; facts_side) (by simp only [K32]; facts_side)
    (Lnew := [(392, 8, wordBytes (r.addr 4708)), (8220, 4, ctrBytes r 2)])
    (fun _ hm' ↦ (storeL r hm' (o := 392) (a := 4708) (by decide) (by decide)).append
      (store4L r hm' (x := .X23) (v := ctr r 2)
        (h.reg (x := .X23) (v := rev32 (ctr r 2)) (by simp [K32])) (by decide) (by decide)))
    (Knew := []) (fun _ _ ↦ trivial)
    (by simp only [L35, L32, L31, L24, L16]; facts_side) (by simp only [K32]; facts_side)
    (bs := pathsRaw r) (by simp [pathsRaw])

/-- **The parsed signature assembled**, `b31 .. b35`. -/
theorem assemble : Seg r b31Offset (fun m ↦ Facts r m (L31 r) (K28 r)) b36Offset
    (fun m ↦ Facts r m (L36 r) (K32 r)) :=
  ((((s31 r hp hc hpre).trans (s32 r hp hc hpre)).trans (s33 r hp hc hpre)).trans
    (s34 r hp hc hpre)).trans (s35 r hp hc hpre)

end

end NativeRustcArm.SphincsVerifyProof.ParseTail
