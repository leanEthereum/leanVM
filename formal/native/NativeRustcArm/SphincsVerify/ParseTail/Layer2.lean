module

public import NativeRustcArm.SphincsVerify.ParseTail.Layer1

/-!
# The parse's tail, layer 2 (`b33 .. b39`)

`b33` loads layer 2's counter (`ctr r 2`, in X24) and the copy loop `b34` copies its chain values
to `8244`; `b35 .. b39` move them by `memcpy` to `26768`, `24720`, `23696`, `22672` and `25744`,
`b35` setting X23 to `8244`, `b36` storing layer 2's path at `16240`, X21 `24720` and X26, X25,
X22 the three counters byte-reversed.
-/

namespace NativeRustcArm.SphincsVerifyProof.ParseTail

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify

set_option Elab.async false

@[expose] public section

/-- `rev` of a counter's low word. -/
def rev32 (v : BitVec 64) : BitVec 64 := UnOp.apply .rev .W32 v

/-- The registers from `b34`'s exit: the three counters. -/
def K34 (r : Run) : List (XReg × BitVec 64) :=
  (.X24, ctr r 2) :: (.X22, ctr r 1) :: (.X21, ctr r 0) :: K0 r

/-- The registers from `b36` on. -/
def K37 (r : Run) : List (XReg × BitVec 64) :=
  (.X21, r.off 24720) :: (.X22, rev32 (ctr r 2)) :: (.X25, rev32 (ctr r 1)) ::
    (.X26, rev32 (ctr r 0)) :: (.X23, r.off 8244) :: (.X24, ctr r 2) :: K0 r

/-- The facts after layer 2, at `b40`. -/
def L40 (r : Run) : List (Nat × Nat × List UInt8) :=
  (25744, 1024, wotsRaw r 2) :: (16240, 160, pathRaw r 2) :: L33 r

end

public section

theorem raw_L33 (r : Run) : (468, 7740, sigBytes r.w) ∈ L33 r := by simp [L33, L25, baseL]

variable (r : Run) [NativeRustcArm.Host] (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees)
  (hpre : r.Pre)
include hp hc hpre

omit hc in
/-- `b33`: layer 2's counter, the copy loop's registers. -/
theorem s33 : Seg r b33Offset (fun m ↦ Facts r m (L33 r) (K27 r)) b34Offset
    (fun m ↦ Facts r m (L33 r) ((.X8, BitVec.ofNat 64 0) :: (.X9, r.off 7024) ::
      (.X24, ctr r 2) :: K27 r)) := fun _ h ↦
  step_fall r hp hpre b33_in_code (by unfold b33; simp) run_b33 rfl rfl rfl h trivial
    (by simp only [L33, L25]; facts_side) (by simp only [K27, K26]; facts_side) (Lnew := [])
    (fun _ _ ↦ trivial) (Knew := [(.X8, BitVec.ofNat 64 0), (.X9, r.off 7024), (.X24, ctr r 2)])
    (fun _ hm' ↦ ⟨reg_lit r hm' rfl, reg_ptr r hm' (a := 7024) rfl,
      reg_load r hm' rfl (by simp [slice, length_sigBytes, sigLayerOff])
        (raw_at r h (raw_L33 r) (k := 6552) (n := 4) (by decide)), trivial⟩)

omit hc in
/-- `b34`: the copy loop, layer 2's chain values to `8244`. -/
theorem s34 : Seg r b34Offset (fun m ↦ Facts r m (L33 r) ((.X8, BitVec.ofNat 64 0) ::
      (.X9, r.off 7024) :: (.X24, ctr r 2) :: K27 r)) b35Offset
    (fun m ↦ Facts r m ((7024, 1024, wotsRaw r 2) :: (8244, 1024, wotsRaw r 2) :: L33 r)
      ((.X9, r.off 7024) :: (.X25, r.off 8244) :: K34 r)) := fun _ h ↦
  copy_loop r hp hpre b34_in_code (by unfold b34; simp) (getElem?_of_infix b34_in_code rfl)
    run_b34 rfl (by simp [wotsRaw, slice, length_sigBytes, sigLayerOff]) (by decide) (by decide)
    (by simp only [L33, L25]; facts_side) (by simp only [K34]; facts_side)
    (((h.weakenK (K' := (.X8, BitVec.ofNat 64 0) :: (.X9, r.off 7024) :: (.X25, r.off 8244) ::
      K34 r) (by simp [K27, K26, K34, K0])).nil 8244).sub_eq (o := 468) (len := 7740)
      (bs := sigBytes r.w) (mem_raw r (raw_L33 r) _) (k := 6556) (n := 1024)
      (o' := 7024) (bs' := wotsRaw r 2) (by decide) rfl rfl)

/-- `b35`: to `26768`, X23 the parsed signature's address. -/
theorem s35 : Seg r b35Offset (fun m ↦ Facts r m ((7024, 1024, wotsRaw r 2) ::
      (8244, 1024, wotsRaw r 2) :: L33 r) ((.X9, r.off 7024) :: (.X25, r.off 8244) :: K34 r)) b36Offset
    (fun m ↦ Facts r m ((26768, 1024, wotsRaw r 2) :: L33 r)
      ((.X23, r.off 8244) :: (.X25, r.off 8244) :: K34 r)) := fun _ h ↦
  Eventually.mono (step_memcpy r hp hc hpre b35_in_code run_b35 rfl rfl rfl
    (a := 26768) (b := 8244) (n := 1024) rfl rfl rfl (by decide) (by decide) (by decide)
    h.dropK trivial (by simp only [L33, L25]; facts_side) (by simp only [K34]; facts_side)
    (Lnew := []) (fun _ _ ↦ trivial)
    (Knew := [(.X23, r.off 8244)]) (fun _ hm' ↦ ⟨reg_ptr r hm' (a := 8244) rfl, trivial⟩)
    (by simp only [L33, L25]; facts_side) (by simp only [K34]; facts_side) (bs := wotsRaw r 2)
    (by simp)) fun _ ⟨hpc, h'⟩ ↦ ⟨hpc, h'.drop1.drop1⟩

/-- `b36`: layer 2's path to `16240`, the values to `24720`, the counters byte-reversed. -/
theorem s36 : Seg r b36Offset (fun m ↦ Facts r m ((26768, 1024, wotsRaw r 2) :: L33 r)
      ((.X23, r.off 8244) :: (.X25, r.off 8244) :: K34 r)) b37Offset
    (fun m ↦ Facts r m ((24720, 1024, wotsRaw r 2) :: (16240, 160, pathRaw r 2) :: L33 r)
      (K37 r)) := fun _ h ↦
  Eventually.mono (step_memcpy r hp hc hpre b36_in_code run_b36 rfl rfl rfl
    (a := 24720) (b := 26768) (n := 1024) rfl rfl rfl (by decide) (by decide) (by decide)
    (h.weakenK (K' := (.X23, r.off 8244) :: (.X24, ctr r 2) :: K0 r) (by simp [K34, K0])) trivial
    (by simp only [L33, L25]; facts_side) (by facts_side)
    (Lnew := [(16240, 160, pathRaw r 2)])
    (fun _ hm' ↦ pathL r h (mem_raw r (raw_L33 r) _) hm' (l := 2) (by decide)
      (by decide) (by decide) (by decide +kernel))
    (Knew := [(.X21, r.off 24720), (.X22, rev32 (ctr r 2)), (.X25, rev32 (ctr r 1)),
      (.X26, rev32 (ctr r 0))])
    (fun _ hm' ↦ ⟨reg_ptr r hm' (a := 24720) rfl,
      (reg_un r hm' (y := .X24) rfl).trans
        (congrArg (UnOp.apply .rev .W32) (h.reg (x := .X24) (v := ctr r 2) (by simp [K34]))),
      (reg_un r hm' (y := .X22) rfl).trans
        (congrArg (UnOp.apply .rev .W32) (h.reg (x := .X22) (v := ctr r 1) (by simp [K34]))),
      (reg_un r hm' (y := .X21) rfl).trans
        (congrArg (UnOp.apply .rev .W32) (h.reg (x := .X21) (v := ctr r 0) (by simp [K34]))),
      trivial⟩)
    (by simp only [L33, L25]; facts_side) (by facts_side) (bs := wotsRaw r 2) (by simp))
    fun _ ⟨hpc, h'⟩ ↦ ⟨hpc, h'.drop2⟩

/-- **Layer 2 of the tail**, `b33 .. b39`. -/
theorem layer2 : Seg r b33Offset (fun m ↦ Facts r m (L33 r) (K27 r)) b40Offset
    (fun m ↦ Facts r m (L40 r) (K37 r)) :=
  ((((((s33 r hp hpre).trans (s34 r hp hpre)).trans (s35 r hp hc hpre)).trans
    (s36 r hp hc hpre)).trans
    (s_copy r hp hc hpre b37_in_code run_b37 rfl rfl rfl (a := 23696) (b := 24720) rfl rfl rfl
      (by decide) (by decide) (by decide) (wotsRaw r 2) ((16240, 160, pathRaw r 2) :: L33 r)
      (K37 r) (by simp only [L33, L25]; facts_side) (by simp only [K37]; facts_side)
      (by simp only [L33, L25]; facts_side) (by simp only [K37]; facts_side))).trans
    (s_copy r hp hc hpre b38_in_code run_b38 rfl rfl rfl (a := 22672) (b := 23696) rfl rfl rfl
      (by decide) (by decide) (by decide) (wotsRaw r 2) ((16240, 160, pathRaw r 2) :: L33 r)
      (K37 r) (by simp only [L33, L25]; facts_side) (by simp only [K37]; facts_side)
      (by simp only [L33, L25]; facts_side) (by simp only [K37]; facts_side))).trans
    (s_copy r hp hc hpre b39_in_code run_b39 rfl rfl rfl (a := 25744) (b := 22672) rfl rfl rfl
      (by decide) (by decide) (by decide) (wotsRaw r 2) ((16240, 160, pathRaw r 2) :: L33 r)
      (K37 r) (by simp only [L33, L25]; facts_side) (by simp only [K37]; facts_side)
      (by simp only [L33, L25]; facts_side) (by simp only [K37]; facts_side))

end

end NativeRustcArm.SphincsVerifyProof.ParseTail
