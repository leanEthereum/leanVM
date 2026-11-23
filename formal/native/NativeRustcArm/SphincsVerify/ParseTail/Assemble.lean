module

public import NativeRustcArm.SphincsVerify.ParseTail.Layer2

/-!
# The parse's tail: the parsed signature assembled at `8244` (`b40 .. b44`)

`b40` stores the randomizer at `12884` and copies the FORS openings to `8244` (X24 `4640`, X20
`4224`); `b41` stores the first layer's address at `392` and copies layer 0's chain values to
`12900`; `b42`, `b43` store layers 0 and 1's counters (byte-reversed) and copy layers 1 and 2's
chain values; `b44` stores layer 2's counter and the paths' address at `376` and copies the 416
bytes of paths to `12468`.
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

/-- The facts from `b41`. -/
def L41 (r : Run) : List (Nat × Nat × List UInt8) :=
  (8244, 4224, forsMem r) :: (12884, 16, r.sig.randomizer) :: L40 r

/-- The registers from `b41`. -/
def K41 (r : Run) : List (XReg × BitVec 64) :=
  (.X24, BitVec.ofNat 64 4640) :: (.X20, BitVec.ofNat 64 4224) :: (.X21, r.off 24720) ::
    (.X22, rev32 (ctr r 2)) :: (.X25, rev32 (ctr r 1)) :: (.X26, rev32 (ctr r 0)) ::
    (.X23, r.off 8244) :: [(.X19, r.off 8208)]

/-- The facts from `b44`. -/
def L44 (r : Run) : List (Nat × Nat × List UInt8) :=
  (14956, 1024, wotsRaw r 2) :: (14952, 4, ctrBytes r 1) :: (13928, 1024, wotsRaw r 1) ::
    (13924, 4, ctrBytes r 0) :: (12900, 1024, wotsRaw r 0) ::
    (392, 8, wordBytes (r.addr 12900)) :: L41 r

/-- The paths: layers 0, 1, 2's. -/
def pathsRaw (r : Run) : List UInt8 := (pathRaw r 0 ++ pathRaw r 1) ++ pathRaw r 2

/-- The facts at `b45`. -/
def L45 (r : Run) : List (Nat × Nat × List UInt8) :=
  (12468, 416, pathsRaw r) :: (376, 8, wordBytes (r.addr 12468)) :: (15980, 4, ctrBytes r 2) ::
    (15984, 128 + 128 + 160, pathsRaw r) :: (15984, 128 + 128, pathRaw r 0 ++ pathRaw r 1) ::
    L44 r

end

public section

variable (r : Run) [NativeRustcArm.Host] (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees)
  (hpre : r.Pre)
include hp hc hpre

/-- `b40`: the randomizer to `12884`, the FORS openings to `8244`. -/
theorem s40 : Seg r b40Offset (fun m ↦ Facts r m (L40 r) (K37 r)) b41Offset
    (fun m ↦ Facts r m (L41 r) (K41 r)) := fun m h ↦
  step_memcpy r hp hc hpre b40_in_code run_b40 rfl rfl rfl
    (a := 8244) (b := 16400) (n := 4224) rfl rfl rfl (by decide) (by decide) (by decide)
    (h.weakenK (K' := (.X21, r.off 24720) :: (.X22, rev32 (ctr r 2)) :: (.X25, rev32 (ctr r 1)) ::
      (.X26, rev32 (ctr r 0)) :: (.X23, r.off 8244) :: [(.X19, r.off 8208)]) (by simp [K37, K0]))
    ⟨(h.reg (x := .X20) (v := r.off 468) (by simp [K37, K0])).trans (ptr_eval r m _ 468).symm,
      trivial⟩
    (by simp only [L40, L33, L25]; facts_side) (by facts_side)
    (Lnew := [(12884, 16, r.sig.randomizer)])
    (fun _ hm' ↦ copyL r h (o' := 27808) (by simp [L40, L33, L25, baseL]) hm' (by decide)
      (by decide +kernel))
    (Knew := [(.X24, BitVec.ofNat 64 4640), (.X20, BitVec.ofNat 64 4224)])
    (fun _ hm' ↦ ⟨reg_lit r hm' rfl, reg_lit r hm' rfl, trivial⟩)
    (by simp only [L40, L33, L25]; facts_side) (by facts_side) (bs := forsMem r)
    (by simp [L40, L33, L25, baseL, forsMem])

/-- `b41`: the first layer's address at `392`, layer 0's chain values to `12900`. -/
theorem s41 : Seg r b41Offset (fun m ↦ Facts r m (L41 r) (K41 r)) b42Offset
    (fun m ↦ Facts r m ((12900, 1024, wotsRaw r 0) :: (392, 8, wordBytes (r.addr 12900)) ::
      L41 r) (K41 r)) := fun m h ↦
  step_memcpy r hp hc hpre b41_in_code run_b41 rfl rfl rfl
    (a := 12900) (b := 21648) (n := 1024) rfl rfl rfl (by decide) (by decide) (by decide) h
    ⟨(h.reg (x := .X23) (v := r.off 8244) (by simp [K41])).trans (ptr_eval r m _ 8244).symm,
      trivial⟩
    (by simp only [L41, L40, L33, L25]; facts_side) (by simp only [K41]; facts_side)
    (Lnew := [(392, 8, wordBytes (r.addr 12900))])
    (fun _ hm' ↦ storeL r hm' (by decide) (by decide))
    (Knew := []) (fun _ _ ↦ trivial)
    (by simp only [L41, L40, L33, L25]; facts_side) (by simp only [K41]; facts_side)
    (bs := wotsRaw r 0) (by simp [L41, L40, L33, L25])

/-- `b42`: layer 0's counter at `13924`, layer 1's chain values to `13928`. -/
theorem s42 : Seg r b42Offset (fun m ↦ Facts r m ((12900, 1024, wotsRaw r 0) ::
      (392, 8, wordBytes (r.addr 12900)) :: L41 r) (K41 r)) b43Offset
    (fun m ↦ Facts r m ((13928, 1024, wotsRaw r 1) :: (13924, 4, ctrBytes r 0) ::
      (12900, 1024, wotsRaw r 0) :: (392, 8, wordBytes (r.addr 12900)) :: L41 r) (K41 r)) :=
  fun m h ↦ step_memcpy r hp hc hpre b42_in_code run_b42 rfl rfl rfl
    (a := 13928) (b := 20624) (n := 1024) rfl rfl rfl (by decide) (by decide) (by decide) h
    ⟨(h.reg (x := .X23) (v := r.off 8244) (by simp [K41])).trans (ptr_eval r m _ 8244).symm,
      trivial⟩
    (by simp only [L41, L40, L33, L25]; facts_side) (by simp only [K41]; facts_side)
    (Lnew := [(13924, 4, ctrBytes r 0)])
    (fun _ hm' ↦ store4L r hm' (x := .X26) (v := ctr r 0)
      (h.reg (x := .X26) (v := rev32 (ctr r 0)) (by simp [K41])) (by decide) (by decide))
    (Knew := []) (fun _ _ ↦ trivial)
    (by simp only [L41, L40, L33, L25]; facts_side) (by simp only [K41]; facts_side)
    (bs := wotsRaw r 1) (by simp [L41, L40, L33])

/-- `b43`: layer 1's counter at `14952`, layer 2's chain values to `14956`. -/
theorem s43 : Seg r b43Offset (fun m ↦ Facts r m ((13928, 1024, wotsRaw r 1) ::
      (13924, 4, ctrBytes r 0) :: (12900, 1024, wotsRaw r 0) ::
      (392, 8, wordBytes (r.addr 12900)) :: L41 r) (K41 r)) b44Offset
    (fun m ↦ Facts r m (L44 r) (K41 r)) :=
  fun m h ↦ step_memcpy r hp hc hpre b43_in_code run_b43 rfl rfl rfl
    (a := 14956) (b := 25744) (n := 1024) rfl rfl rfl (by decide) (by decide) (by decide) h
    ⟨(h.reg (x := .X23) (v := r.off 8244) (by simp [K41])).trans (ptr_eval r m _ 8244).symm,
      trivial⟩
    (by simp only [L41, L40, L33, L25]; facts_side) (by simp only [K41]; facts_side)
    (Lnew := [(14952, 4, ctrBytes r 1)])
    (fun _ hm' ↦ store4L r hm' (x := .X25) (v := ctr r 1)
      (h.reg (x := .X25) (v := rev32 (ctr r 1)) (by simp [K41])) (by decide) (by decide))
    (Knew := []) (fun _ _ ↦ trivial)
    (by simp only [L41, L40, L33, L25]; facts_side) (by simp only [K41]; facts_side)
    (bs := wotsRaw r 2) (by simp [L41, L40])

/-- `b44`: layer 2's counter at `15980`, the paths' address at `376`, the paths to `12468`. -/
theorem s44 : Seg r b44Offset (fun m ↦ Facts r m (L44 r) (K41 r)) b45Offset
    (fun m ↦ Facts r m (L45 r) (K41 r)) := fun m h ↦
  step_memcpy r hp hc hpre b44_in_code run_b44 rfl rfl rfl
    (a := 12468) (b := 15984) (n := 416) rfl rfl rfl (by decide) (by decide) (by decide)
    ((h.concat (o := 15984) (n := 128) (n' := 128) (xs := pathRaw r 0) (ys := pathRaw r 1)
      (by simp [L44, L41, L40, L33, L25]) (by simp [L44, L41, L40, L33])).concat
      (o := 15984) (n := 128 + 128) (n' := 160) (xs := pathRaw r 0 ++ pathRaw r 1)
      (ys := pathRaw r 2) List.mem_cons_self (by simp [L44, L41, L40]))
    ⟨(h.reg (x := .X23) (v := r.off 8244) (by simp [K41])).trans (ptr_eval r m _ 8244).symm,
      h.reg (x := .X20) (v := BitVec.ofNat 64 4224) (by simp [K41]), trivial⟩
    (by simp only [L44, L41, L40, L33, L25]; facts_side) (by simp only [K41]; facts_side)
    (Lnew := [(376, 8, wordBytes (r.addr 12468)), (15980, 4, ctrBytes r 2)])
    (fun _ hm' ↦ (storeL r hm' (o := 376) (a := 12468) (by decide) (by decide)).append
      (store4L r hm' (x := .X22) (v := ctr r 2)
        (h.reg (x := .X22) (v := rev32 (ctr r 2)) (by simp [K41])) (by decide) (by decide)))
    (Knew := []) (fun _ _ ↦ trivial)
    (by simp only [L44, L41, L40, L33, L25]; facts_side) (by simp only [K41]; facts_side)
    (bs := pathsRaw r) (by simp [pathsRaw])

/-- **The parsed signature assembled**, `b40 .. b44`. -/
theorem assemble : Seg r b40Offset (fun m ↦ Facts r m (L40 r) (K37 r)) b45Offset
    (fun m ↦ Facts r m (L45 r) (K41 r)) :=
  ((((s40 r hp hc hpre).trans (s41 r hp hc hpre)).trans (s42 r hp hc hpre)).trans
    (s43 r hp hc hpre)).trans (s44 r hp hc hpre)

end

end NativeRustcArm.SphincsVerifyProof.ParseTail
