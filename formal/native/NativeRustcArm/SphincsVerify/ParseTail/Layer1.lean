module

public import NativeRustcArm.SphincsVerify.ParseTail.Layer0

/-!
# The parse's tail, layer 1 (`b25 .. b32`)

`b25` loads layer 1's counter (`ctr r 1`, in X22) and the copy loop `b26` copies its chain values
to `8244`; `b27 .. b32` move them by `memcpy` to `26768`, `24720`, `23696`, `22672`, `25744` and
`20624`, `b27` setting X25 to `8244`, `b28` storing layer 1's path at `16112`.
-/

namespace NativeRustcArm.SphincsVerifyProof.ParseTail

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify

set_option Elab.async false

@[expose] public section

/-- The registers from `b26`: the counters loaded so far, X23 the paths' scratch. -/
def K26 (r : Run) : List (XReg × BitVec 64) :=
  (.X22, ctr r 1) :: (.X21, ctr r 0) :: (.X23, r.off 15984) :: K0 r

/-- The registers from `b27` on. -/
def K27 (r : Run) : List (XReg × BitVec 64) := (.X25, r.off 8244) :: K26 r

/-- The facts after layer 1, at `b33`. -/
def L33 (r : Run) : List (Nat × Nat × List UInt8) :=
  (20624, 1024, wotsRaw r 1) :: (16112, 128, pathRaw r 1) :: L25 r

end

public section

theorem raw_L25 (r : Run) : (468, 7740, sigBytes r.w) ∈ L25 r := by simp [L25, baseL]

variable (r : Run) [NativeRustcArm.Host] (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees)
  (hpre : r.Pre)
include hp hc hpre

omit hc in
/-- `b25`: layer 1's counter, the copy loop's registers. -/
theorem s25 : Seg r b25Offset (fun m ↦ Facts r m (L25 r) (K25 r)) b26Offset
    (fun m ↦ Facts r m (L25 r) ((.X8, BitVec.ofNat 64 0) :: (.X9, r.off 5868) ::
      (.X22, ctr r 1) :: K25 r)) := fun m h ↦
  step_fall r hp hpre b25_in_code (by unfold b25; simp) run_b25 rfl rfl rfl h
    ⟨(h.reg (x := .X25) (v := r.off 468) (by simp [K25])).trans (ptr_eval r m _ 468).symm, trivial⟩
    (by simp only [L25]; facts_side) (by simp only [K25]; facts_side) (Lnew := [])
    (fun _ _ ↦ trivial) (Knew := [(.X8, BitVec.ofNat 64 0), (.X9, r.off 5868), (.X22, ctr r 1)])
    (fun _ hm' ↦ ⟨reg_lit r hm' rfl, reg_ptr r hm' (a := 5868) rfl,
      reg_load r hm' rfl (by simp [slice, length_sigBytes, sigLayerOff])
        (raw_at r h (raw_L25 r) (k := 5396) (n := 4) (by decide)), trivial⟩)

omit hc in
/-- `b26`: the copy loop, layer 1's chain values to `8244`. -/
theorem s26 : Seg r b26Offset (fun m ↦ Facts r m (L25 r) ((.X8, BitVec.ofNat 64 0) ::
      (.X9, r.off 5868) :: (.X22, ctr r 1) :: K25 r)) b27Offset
    (fun m ↦ Facts r m ((5868, 1024, wotsRaw r 1) :: (8244, 1024, wotsRaw r 1) :: L25 r)
      ((.X9, r.off 5868) :: (.X24, r.off 8244) :: K26 r)) := fun _ h ↦
  copy_loop r hp hpre b26_in_code (by unfold b26; simp) (getElem?_of_infix b26_in_code rfl)
    run_b26 rfl (by simp [wotsRaw, slice, length_sigBytes, sigLayerOff]) (by decide) (by decide)
    (by simp only [L25]; facts_side) (by simp only [K26]; facts_side)
    (((h.weakenK (K' := (.X8, BitVec.ofNat 64 0) :: (.X9, r.off 5868) :: (.X24, r.off 8244) ::
      K26 r) (by simp [K25, K26, K0])).nil 8244).sub_eq (o := 468) (len := 7740)
      (bs := sigBytes r.w) (mem_raw r (raw_L25 r) _) (k := 5400) (n := 1024)
      (o' := 5868) (bs' := wotsRaw r 1) (by decide) rfl rfl)

/-- `b27`: to `26768`, X25 the parsed signature's address. -/
theorem s27 : Seg r b27Offset (fun m ↦ Facts r m ((5868, 1024, wotsRaw r 1) ::
      (8244, 1024, wotsRaw r 1) :: L25 r) ((.X9, r.off 5868) :: (.X24, r.off 8244) :: K26 r)) b28Offset
    (fun m ↦ Facts r m ((26768, 1024, wotsRaw r 1) :: L25 r) (K27 r)) := fun _ h ↦
  Eventually.mono (step_memcpy r hp hc hpre b27_in_code run_b27 rfl rfl rfl
    (a := 26768) (b := 8244) (n := 1024) rfl rfl rfl (by decide) (by decide) (by decide)
    h.dropK.dropK trivial (by simp only [L25]; facts_side) (by simp only [K26]; facts_side)
    (Lnew := []) (fun _ _ ↦ trivial)
    (Knew := [(.X25, r.off 8244)]) (fun _ hm' ↦ ⟨reg_ptr r hm' (a := 8244) rfl, trivial⟩)
    (by simp only [L25]; facts_side) (by simp only [K26]; facts_side) (bs := wotsRaw r 1)
    (by simp)) fun _ ⟨hpc, h'⟩ ↦ ⟨hpc, h'.drop1.drop1⟩

/-- `b28`: layer 1's path to `16112`, the values to `24720`. -/
theorem s28 : Seg r b28Offset (fun m ↦ Facts r m ((26768, 1024, wotsRaw r 1) :: L25 r) (K27 r)) b29Offset
    (fun m ↦ Facts r m ((24720, 1024, wotsRaw r 1) :: (16112, 128, pathRaw r 1) :: L25 r)
      (K27 r)) := fun m h ↦
  Eventually.mono (step_memcpy r hp hc hpre b28_in_code run_b28 rfl rfl rfl
    (a := 24720) (b := 26768) (n := 1024) rfl rfl rfl (by decide) (by decide) (by decide)
    h ⟨(h.reg (x := .X20) (v := r.off 468) (by simp [K27, K26, K0])).trans
        (ptr_eval r m _ 468).symm,
      (h.reg (x := .X23) (v := r.off 15984) (by simp [K27, K26])).trans
        (ptr_eval r m _ 15984).symm, trivial⟩
    (by simp only [L25]; facts_side) (by simp only [K27, K26]; facts_side)
    (Lnew := [(16112, 128, pathRaw r 1)])
    (fun _ hm' ↦ pathL r h (mem_raw r (raw_L25 r) _) hm' (l := 1) (by decide)
      (by decide) (by decide) (by decide +kernel))
    (Knew := []) (fun _ _ ↦ trivial)
    (by simp only [L25]; facts_side) (by simp only [K27, K26]; facts_side) (bs := wotsRaw r 1)
    (by simp)) fun _ ⟨hpc, h'⟩ ↦ ⟨hpc, h'.drop2⟩

/-- **Layer 1 of the tail**, `b25 .. b32`. -/
theorem layer1 : Seg r b25Offset (fun m ↦ Facts r m (L25 r) (K25 r)) b33Offset
    (fun m ↦ Facts r m (L33 r) (K27 r)) :=
  (((((((s25 r hp hpre).trans (s26 r hp hpre)).trans (s27 r hp hc hpre)).trans
    (s28 r hp hc hpre)).trans
    (s_copy r hp hc hpre b29_in_code run_b29 rfl rfl rfl (a := 23696) (b := 24720) rfl rfl rfl
      (by decide) (by decide) (by decide) (wotsRaw r 1) ((16112, 128, pathRaw r 1) :: L25 r)
      (K27 r) (by simp only [L25]; facts_side) (by simp only [K27, K26]; facts_side)
      (by simp only [L25]; facts_side) (by simp only [K27, K26]; facts_side))).trans
    (s_copy r hp hc hpre b30_in_code run_b30 rfl rfl rfl (a := 22672) (b := 23696) rfl rfl rfl
      (by decide) (by decide) (by decide) (wotsRaw r 1) ((16112, 128, pathRaw r 1) :: L25 r)
      (K27 r) (by simp only [L25]; facts_side) (by simp only [K27, K26]; facts_side)
      (by simp only [L25]; facts_side) (by simp only [K27, K26]; facts_side))).trans
    (s_copy r hp hc hpre b31_in_code run_b31 rfl rfl rfl (a := 25744) (b := 22672) rfl rfl rfl
      (by decide) (by decide) (by decide) (wotsRaw r 1) ((16112, 128, pathRaw r 1) :: L25 r)
      (K27 r) (by simp only [L25]; facts_side) (by simp only [K27, K26]; facts_side)
      (by simp only [L25]; facts_side) (by simp only [K27, K26]; facts_side))).trans
    (s_copy r hp hc hpre b32_in_code run_b32 rfl rfl rfl (a := 20624) (b := 25744) rfl rfl rfl
      (by decide) (by decide) (by decide) (wotsRaw r 1) ((16112, 128, pathRaw r 1) :: L25 r)
      (K27 r) (by simp only [L25]; facts_side) (by simp only [K27, K26]; facts_side)
      (by simp only [L25]; facts_side) (by simp only [K27, K26]; facts_side))

end

end NativeRustcArm.SphincsVerifyProof.ParseTail
