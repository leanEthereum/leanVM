module

public import NativeRustcArm.SphincsVerify.ParseTail.Layer1

/-!
# The parse's tail, layer 2 (`b24 .. b30`)

`b24` loads layer 2's counter (`ctr r 2`, in X26) and the copy loop `b25` copies its chain values
to `484`; `b26 .. b30` move them by `memcpy` to `19008`, `16960`, `15936`, `14912` and `17984`,
`b26` setting X25 to `484`, `b27` storing layer 2's path at `8480`, X19 `16960` and X28, X24, X23
the three counters byte-reversed.
-/

namespace NativeRustcArm.SphincsVerifyProof.ParseTail

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify

set_option Elab.async false

@[expose] public section

/-- `rev` of a counter's low word. -/
def rev32 (v : BitVec 64) : BitVec 64 := UnOp.apply .rev .W32 v

/-- The registers from `b25`'s exit: the three counters. -/
def K25 (r : Run) : List (XReg × BitVec 64) :=
  (.X26, ctr r 2) :: (.X24, ctr r 1) :: (.X23, ctr r 0) :: K0 r

/-- The registers from `b27` on. -/
def K28 (r : Run) : List (XReg × BitVec 64) :=
  (.X19, r.off 16960) :: (.X23, rev32 (ctr r 2)) :: (.X24, rev32 (ctr r 1)) ::
    (.X28, rev32 (ctr r 0)) :: (.X25, r.off 484) ::
    [(.X20, r.off 448), (.X21, r.msgPtr), (.X22, r.off 484)]

/-- The facts after layer 2, at `b31`. -/
def L31 (r : Run) : List (Nat × Nat × List UInt8) :=
  (17984, 1024, wotsRaw r 2) :: (8480, 160, pathRaw r 2) :: L24 r

end

public section

variable (r : Run) [NativeRustcArm.Host] (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees)
  (hpre : r.Pre)
include hp hc hpre

omit hc in
/-- `b24`: layer 2's counter, the copy loop's registers. -/
theorem s24 : Seg r b24Offset (fun m ↦ Facts r m (L24 r) (K18 r)) b25Offset
    (fun m ↦ Facts r m (L24 r) ((.X8, BitVec.ofNat 64 0) :: (.X9, r.sigPtr + BitVec.ofNat 64 6556) ::
      (.X26, ctr r 2) :: K18 r)) := fun m h ↦
  step_fall r hp hpre b24_in_code (by unfold b24; simp) run_b24 rfl rfl rfl h
    ⟨(h.reg (x := .X19) (v := r.sigPtr) (by simp [K18, K17, K0])).trans (by show _ = r.sigPtr + BitVec.ofInt 64 0; simp), trivial⟩
    (by simp only [L24, L16]; facts_side) (by simp only [K18, K17]; facts_side) (Lnew := [])
    (fun _ _ ↦ trivial)
    (Knew := [(.X8, BitVec.ofNat 64 0), (.X9, r.sigPtr + BitVec.ofNat 64 6556), (.X26, ctr r 2)])
    (fun _ hm' ↦ ⟨reg_lit r hm' rfl, reg_ptr1 r hm' (a := 6556) rfl,
      reg_load1 r hm' rfl (by simp [slice, r.hsig, sigLayerOff])
        (Parse.bytesAt_sig_sub r hpre h.1.2.2.2.1 (s := 6552) (k := 4) (by decide)), trivial⟩)

omit hc in
/-- `b25`: the copy loop, layer 2's chain values to `484`. -/
theorem s25 : Seg r b25Offset (fun m ↦ Facts r m (L24 r) ((.X8, BitVec.ofNat 64 0) ::
      (.X9, r.sigPtr + BitVec.ofNat 64 6556) :: (.X26, ctr r 2) :: K18 r)) b26Offset
    (fun m ↦ Facts r m ((484, 1024, wotsRaw r 2) :: L24 r)
      ((.X9, r.sigPtr + BitVec.ofNat 64 6556) :: (.X28, r.off 484) :: K25 r)) := fun _ h ↦
  copy_loop r hp hpre b25_in_code (by unfold b25; simp) (getElem?_of_infix b25_in_code rfl)
    run_b25 rfl (src := 6556) (by decide)
    (by simp only [L24, L16]; facts_side) (by simp only [K25]; facts_side)
    ((h.weakenK (K' := (.X8, BitVec.ofNat 64 0) :: (.X9, r.sigPtr + BitVec.ofNat 64 6556) ::
      (.X28, r.off 484) :: K25 r) (by simp [K18, K17, K25, K0])).nil 484)

/-- `b26`: to `19008`, X25 the parsed signature's address. -/
theorem s26 : Seg r b26Offset (fun m ↦ Facts r m ((484, 1024, wotsRaw r 2) :: L24 r)
      ((.X9, r.sigPtr + BitVec.ofNat 64 6556) :: (.X28, r.off 484) :: K25 r)) b27Offset
    (fun m ↦ Facts r m ((19008, 1024, wotsRaw r 2) :: L24 r)
      ((.X25, r.off 484) :: K25 r)) := fun _ h ↦
  Eventually.mono (step_memcpy r hp hc hpre b26_in_code run_b26 rfl rfl rfl
    (a := 19008) (b := 484) (n := 1024) rfl rfl rfl (by decide) (by decide) (by decide)
    h.dropK.dropK trivial (by simp only [L24, L16]; facts_side) (by simp only [K25]; facts_side)
    (Lnew := []) (fun _ _ ↦ trivial)
    (Knew := [(.X25, r.off 484)]) (fun _ hm' ↦ ⟨reg_ptr r hm' (a := 484) rfl, trivial⟩)
    (by simp only [L24, L16]; facts_side) (by simp only [K25]; facts_side) (bs := wotsRaw r 2)
    (by simp)) fun _ ⟨hpc, h'⟩ ↦ ⟨hpc, h'.drop1⟩

/-- `b27`: layer 2's path to `8480`, the values to `16960`, the counters byte-reversed, X19 `16960`. -/
theorem s27 : Seg r b27Offset (fun m ↦ Facts r m ((19008, 1024, wotsRaw r 2) :: L24 r)
      ((.X25, r.off 484) :: K25 r)) b28Offset
    (fun m ↦ Facts r m ((16960, 1024, wotsRaw r 2) :: (8480, 160, pathRaw r 2) :: L24 r)
      (K28 r)) := fun m h ↦
  Eventually.mono (step_memcpy r hp hc hpre b27_in_code run_b27 rfl rfl rfl
    (a := 16960) (b := 19008) (n := 1024) rfl rfl rfl (by decide) (by decide) (by decide)
    (h.weakenK (K' := (.X25, r.off 484) :: [(.X20, r.off 448), (.X21, r.msgPtr), (.X22, r.off 484)])
      (by simp [K25, K0]))
    ⟨(h.reg (x := .X19) (v := r.sigPtr) (by simp [K25, K0])).trans (by show _ = r.sigPtr + BitVec.ofInt 64 0; simp), trivial⟩
    (by simp only [L24, L16]; facts_side) (by facts_side)
    (Lnew := [(8480, 160, pathRaw r 2)])
    (fun _ hm' ↦ pathL r hpre h.1 hm' (l := 2) (by decide) (by decide) (by decide) (by decide +kernel))
    (Knew := [(.X19, r.off 16960), (.X23, rev32 (ctr r 2)), (.X24, rev32 (ctr r 1)),
      (.X28, rev32 (ctr r 0))])
    (fun _ hm' ↦ ⟨reg_ptr r hm' (a := 16960) rfl,
      (reg_un r hm' (y := .X26) rfl).trans
        (congrArg (UnOp.apply .rev .W32) (h.reg (x := .X26) (v := ctr r 2) (by simp [K25]))),
      (reg_un r hm' (y := .X24) rfl).trans
        (congrArg (UnOp.apply .rev .W32) (h.reg (x := .X24) (v := ctr r 1) (by simp [K25]))),
      (reg_un r hm' (y := .X23) rfl).trans
        (congrArg (UnOp.apply .rev .W32) (h.reg (x := .X23) (v := ctr r 0) (by simp [K25]))),
      trivial⟩)
    (by simp only [L24, L16]; facts_side) (by facts_side) (bs := wotsRaw r 2) (by simp))
    fun _ ⟨hpc, h'⟩ ↦ ⟨hpc, h'.drop2⟩

/-- **Layer 2 of the tail**, `b24 .. b30`. -/
theorem layer2 : Seg r b24Offset (fun m ↦ Facts r m (L24 r) (K18 r)) b31Offset
    (fun m ↦ Facts r m (L31 r) (K28 r)) :=
  ((((((s24 r hp hpre).trans (s25 r hp hpre)).trans (s26 r hp hc hpre)).trans
    (s27 r hp hc hpre)).trans
    (s_copy r hp hc hpre b28_in_code run_b28 rfl rfl rfl (a := 15936) (b := 16960) rfl rfl rfl
      (by decide) (by decide) (by decide) (wotsRaw r 2) ((8480, 160, pathRaw r 2) :: L24 r)
      (K28 r) (by simp only [L24, L16]; facts_side) (by simp only [K28]; facts_side)
      (by simp only [L24, L16]; facts_side) (by simp only [K28]; facts_side))).trans
    (s_copy r hp hc hpre b29_in_code run_b29 rfl rfl rfl (a := 14912) (b := 15936) rfl rfl rfl
      (by decide) (by decide) (by decide) (wotsRaw r 2) ((8480, 160, pathRaw r 2) :: L24 r)
      (K28 r) (by simp only [L24, L16]; facts_side) (by simp only [K28]; facts_side)
      (by simp only [L24, L16]; facts_side) (by simp only [K28]; facts_side))).trans
    (s_copy r hp hc hpre b30_in_code run_b30 rfl rfl rfl (a := 17984) (b := 14912) rfl rfl rfl
      (by decide) (by decide) (by decide) (wotsRaw r 2) ((8480, 160, pathRaw r 2) :: L24 r)
      (K28 r) (by simp only [L24, L16]; facts_side) (by simp only [K28]; facts_side)
      (by simp only [L24, L16]; facts_side) (by simp only [K28]; facts_side))

end

end NativeRustcArm.SphincsVerifyProof.ParseTail
