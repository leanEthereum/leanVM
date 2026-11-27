module

public import NativeRustcArm.SphincsVerify.ParseTail.Layer0

/-!
# The parse's tail, layer 1 (`b16 .. b23`)

`b16` loads layer 1's counter (`ctr r 1`, in X24) and the copy loop `b17` copies its chain values
to `484`; `b18 .. b23` move them by `memcpy` to `19008`, `16960`, `15936`, `14912`, `17984` and
`12864`, `b18` setting X28 to `484`, `b19` storing layer 1's path at `8352`.
-/

namespace NativeRustcArm.SphincsVerifyProof.ParseTail

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify

set_option Elab.async false

@[expose] public section

/-- The registers from `b17`: the counters loaded so far, X25 the paths' scratch. -/
def K17 (r : Run) : List (XReg × BitVec 64) :=
  (.X24, ctr r 1) :: (.X23, ctr r 0) :: (.X25, r.off 8224) :: K0 r

/-- The registers from `b18` on. -/
def K18 (r : Run) : List (XReg × BitVec 64) := (.X28, r.off 484) :: K17 r

/-- The facts after layer 1, at `b24`. -/
def L24 (r : Run) : List (Nat × Nat × List UInt8) :=
  (12864, 1024, wotsRaw r 1) :: (8352, 128, pathRaw r 1) :: L16 r

end

public section

variable (r : Run) [ElfHost] (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees)
  (hpre : r.Pre)
include hp hc hpre

omit hc in
/-- `b16`: layer 1's counter, the copy loop's registers. -/
theorem s16 : Seg r b16Offset (fun m ↦ Facts r m (L16 r) (K16 r)) b17Offset
    (fun m ↦ Facts r m (L16 r) ((.X8, BitVec.ofNat 64 0) :: (.X9, r.sigPtr + BitVec.ofNat 64 5400) ::
      (.X24, ctr r 1) :: K16 r)) := fun m h ↦
  step_fall r hp hpre b16_in_code (by unfold b16; simp) run_b16 rfl rfl rfl h
    ⟨(h.reg (x := .X19) (v := r.sigPtr) (by simp [K16, K0])).trans (by show _ = r.sigPtr + BitVec.ofInt 64 0; simp), trivial⟩
    (by simp only [L16]; facts_side) (by simp only [K16]; facts_side) (Lnew := [])
    (fun _ _ ↦ trivial)
    (Knew := [(.X8, BitVec.ofNat 64 0), (.X9, r.sigPtr + BitVec.ofNat 64 5400), (.X24, ctr r 1)])
    (fun _ hm' ↦ ⟨reg_lit r hm' rfl, reg_ptr1 r hm' (a := 5400) rfl,
      reg_load1 r hm' rfl (by simp [slice, r.hsig, sigLayerOff])
        (Parse.bytesAt_sig_sub r hpre h.1.2.2.2.1 (s := 5396) (k := 4) (by decide)), trivial⟩)

omit hc in
/-- `b17`: the copy loop, layer 1's chain values to `484`. -/
theorem s17 : Seg r b17Offset (fun m ↦ Facts r m (L16 r) ((.X8, BitVec.ofNat 64 0) ::
      (.X9, r.sigPtr + BitVec.ofNat 64 5400) :: (.X24, ctr r 1) :: K16 r)) b18Offset
    (fun m ↦ Facts r m ((484, 1024, wotsRaw r 1) :: L16 r)
      ((.X9, r.sigPtr + BitVec.ofNat 64 5400) :: (.X26, r.off 484) :: K17 r)) := fun _ h ↦
  copy_loop r hp hpre b17_in_code (by unfold b17; simp) (getElem?_of_infix b17_in_code rfl)
    run_b17 rfl (src := 5400) (by decide)
    (by simp only [L16]; facts_side) (by simp only [K17]; facts_side)
    ((h.weakenK (K' := (.X8, BitVec.ofNat 64 0) :: (.X9, r.sigPtr + BitVec.ofNat 64 5400) ::
      (.X26, r.off 484) :: K17 r) (by simp [K16, K17, K0])).nil 484)

/-- `b18`: to `19008`, X28 = `484`. -/
theorem s18 : Seg r b18Offset (fun m ↦ Facts r m ((484, 1024, wotsRaw r 1) :: L16 r)
      ((.X9, r.sigPtr + BitVec.ofNat 64 5400) :: (.X26, r.off 484) :: K17 r)) b19Offset
    (fun m ↦ Facts r m ((19008, 1024, wotsRaw r 1) :: L16 r) (K18 r)) := fun _ h ↦
  Eventually.mono_elf (step_memcpy r hp hc hpre b18_in_code run_b18 rfl rfl rfl
    (a := 19008) (b := 484) (n := 1024) rfl rfl rfl (by decide) (by decide) (by decide)
    h.dropK.dropK trivial (by simp only [L16]; facts_side) (by simp only [K17]; facts_side)
    (Lnew := []) (fun _ _ ↦ trivial)
    (Knew := [(.X28, r.off 484)]) (fun _ hm' ↦ ⟨reg_ptr r hm' (a := 484) rfl, trivial⟩)
    (by simp only [L16]; facts_side) (by simp only [K17]; facts_side) (bs := wotsRaw r 1)
    (by simp)) fun _ ⟨hpc, h'⟩ ↦ ⟨hpc, h'.drop1⟩

/-- `b19`: layer 1's path to `8352`, the values to `16960`. -/
theorem s19 : Seg r b19Offset (fun m ↦ Facts r m ((19008, 1024, wotsRaw r 1) :: L16 r) (K18 r)) b20Offset
    (fun m ↦ Facts r m ((16960, 1024, wotsRaw r 1) :: (8352, 128, pathRaw r 1) :: L16 r)
      (K18 r)) := fun m h ↦
  Eventually.mono_elf (step_memcpy r hp hc hpre b19_in_code run_b19 rfl rfl rfl
    (a := 16960) (b := 19008) (n := 1024) rfl rfl rfl (by decide) (by decide) (by decide)
    h ⟨(h.reg (x := .X19) (v := r.sigPtr) (by simp [K18, K17, K0])).trans (by show _ = r.sigPtr + BitVec.ofInt 64 0; simp),
      (h.reg (x := .X25) (v := r.off 8224) (by simp [K18, K17])).trans
        (ptr_eval r m _ 8224).symm, trivial⟩
    (by simp only [L16]; facts_side) (by simp only [K18, K17]; facts_side)
    (Lnew := [(8352, 128, pathRaw r 1)])
    (fun _ hm' ↦ pathL r hpre h.1 hm' (l := 1) (by decide) (by decide) (by decide) (by decide +kernel))
    (Knew := []) (fun _ _ ↦ trivial)
    (by simp only [L16]; facts_side) (by simp only [K18, K17]; facts_side) (bs := wotsRaw r 1)
    (by simp)) fun _ ⟨hpc, h'⟩ ↦ ⟨hpc, h'.drop2⟩

/-- **Layer 1 of the tail**, `b16 .. b23`. -/
theorem layer1 : Seg r b16Offset (fun m ↦ Facts r m (L16 r) (K16 r)) b24Offset
    (fun m ↦ Facts r m (L24 r) (K18 r)) :=
  (((((((s16 r hp hpre).trans (s17 r hp hpre)).trans (s18 r hp hc hpre)).trans
    (s19 r hp hc hpre)).trans
    (s_copy r hp hc hpre b20_in_code run_b20 rfl rfl rfl (a := 15936) (b := 16960) rfl rfl rfl
      (by decide) (by decide) (by decide) (wotsRaw r 1) ((8352, 128, pathRaw r 1) :: L16 r)
      (K18 r) (by simp only [L16]; facts_side) (by simp only [K18, K17]; facts_side)
      (by simp only [L16]; facts_side) (by simp only [K18, K17]; facts_side))).trans
    (s_copy r hp hc hpre b21_in_code run_b21 rfl rfl rfl (a := 14912) (b := 15936) rfl rfl rfl
      (by decide) (by decide) (by decide) (wotsRaw r 1) ((8352, 128, pathRaw r 1) :: L16 r)
      (K18 r) (by simp only [L16]; facts_side) (by simp only [K18, K17]; facts_side)
      (by simp only [L16]; facts_side) (by simp only [K18, K17]; facts_side))).trans
    (s_copy r hp hc hpre b22_in_code run_b22 rfl rfl rfl (a := 17984) (b := 14912) rfl rfl rfl
      (by decide) (by decide) (by decide) (wotsRaw r 1) ((8352, 128, pathRaw r 1) :: L16 r)
      (K18 r) (by simp only [L16]; facts_side) (by simp only [K18, K17]; facts_side)
      (by simp only [L16]; facts_side) (by simp only [K18, K17]; facts_side))).trans
    (s_copy r hp hc hpre b23_in_code run_b23 rfl rfl rfl (a := 12864) (b := 17984) rfl rfl rfl
      (by decide) (by decide) (by decide) (wotsRaw r 1) ((8352, 128, pathRaw r 1) :: L16 r)
      (K18 r) (by simp only [L16]; facts_side) (by simp only [K18, K17]; facts_side)
      (by simp only [L16]; facts_side) (by simp only [K18, K17]; facts_side))

end

end NativeRustcArm.SphincsVerifyProof.ParseTail
