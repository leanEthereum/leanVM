module

public import NativeRustcArm.Code.Common.Memcpy.Names

public import NativeRustcArm.SphincsVerify.ParseTail.State

/-!
# The parse's tail, layer 0 (`b16 .. b24`)

`b16` zeroes the paths' last 288 bytes; `b17` loads layer 0's counter (`ctr r 0`, in X21) and the
copy loop `b18` copies its chain values to `8244`; `b19 .. b24` move them by `memcpy` to `26768`,
`24720`, `23696`, `22672`, `25744` and `21648`, `b20` storing layer 0's path at `15984` and X25 the
raw signature. One segment per block (`s16` .. `s24`), then `layer0`.
-/

namespace NativeRustcArm.SphincsVerifyProof.ParseTail

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify

set_option Elab.async false

@[expose] public section

/-- The facts after layer 0, at `b25`. -/
def L25 (r : Run) : List (Nat × Nat × List UInt8) :=
  (21648, 1024, wotsRaw r 0) :: (15984, 128, pathRaw r 0) :: baseL r

/-- The registers after layer 0. -/
def K25 (r : Run) : List (XReg × BitVec 64) :=
  (.X25, r.off 468) :: (.X24, r.off 8244) :: (.X21, ctr r 0) :: (.X23, r.off 15984) :: K0 r

/-- The registers from `b19` to `b20`. -/
def K19 (r : Run) : List (XReg × BitVec 64) :=
  (.X24, r.off 8244) :: (.X21, ctr r 0) :: (.X23, r.off 15984) :: K0 r

/-- The registers from `b21` on (layer 0's: `K25`). -/
def K21 (r : Run) : List (XReg × BitVec 64) := (.X25, r.off 468) :: K19 r

end

public section

variable (r : Run)

variable [NativeRustcArm.Host] (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
include hp hc hpre

/-- `b16`: the paths' last 288 bytes zeroed. -/
theorem s16 : Seg r b16Offset (fun m ↦ Facts r m (baseL r) (K0 r)) b17Offset
    (fun m ↦ Facts r m (baseL r) ((.X23, r.off 15984) :: K0 r)) := fun _ h ↦
  step_memset r hp hc hpre b16_in_code run_b16 rfl rfl rfl (a := 16112) (n := 288) rfl rfl
    (by decide) h trivial (by facts_side) (by facts_side) (Knew := [(.X23, r.off 15984)])
    (fun _ hm' ↦ ⟨reg_ptr r hm' (a := 15984) rfl, trivial⟩) (by facts_side) (by facts_side)

omit hc in
/-- `b17`: layer 0's counter, the copy loop's registers. -/
theorem s17 : Seg r b17Offset (fun m ↦ Facts r m (baseL r) ((.X23, r.off 15984) :: K0 r)) b18Offset
    (fun m ↦ Facts r m (baseL r) ((.X8, BitVec.ofNat 64 0) :: (.X9, r.off 4712) ::
      (.X10, r.off 8244) :: (.X21, ctr r 0) :: (.X23, r.off 15984) :: K0 r)) := fun _ h ↦
  step_fall r hp hpre b17_in_code (by unfold b17; simp) run_b17 rfl rfl rfl h trivial
    (by facts_side) (by facts_side) (Lnew := []) (fun _ _ ↦ trivial)
    (Knew := [(.X8, BitVec.ofNat 64 0), (.X9, r.off 4712), (.X10, r.off 8244), (.X21, ctr r 0)])
    (fun _ hm' ↦ ⟨reg_lit r hm' rfl, reg_ptr r hm' (a := 4712) rfl, reg_ptr r hm' (a := 8244) rfl,
      reg_load r hm' rfl (by simp [slice, length_sigBytes, sigLayerOff])
        (raw_at r h (raw_baseL r) (k := 4240) (n := 4) (by decide)), trivial⟩)

omit hc in
/-- `b18`: the copy loop, layer 0's chain values to `8244`. -/
theorem s18 : Seg r b18Offset (fun m ↦ Facts r m (baseL r) ((.X8, BitVec.ofNat 64 0) ::
      (.X9, r.off 4712) :: (.X10, r.off 8244) :: (.X21, ctr r 0) :: (.X23, r.off 15984) :: K0 r)) b19Offset
    (fun m ↦ Facts r m ((4712, 1024, wotsRaw r 0) :: (8244, 1024, wotsRaw r 0) :: baseL r)
      ((.X9, r.off 4712) :: (.X10, r.off 8244) :: (.X21, ctr r 0) :: (.X23, r.off 15984) :: K0 r)) :=
  fun _ h ↦ copy_loop r hp hpre b18_in_code (by unfold b18; simp)
    (getElem?_of_infix b18_in_code rfl) run_b18 rfl
    (by simp [wotsRaw, slice, length_sigBytes, sigLayerOff]) (by decide) (by decide)
    (by facts_side) (by facts_side)
    ((h.nil 8244).sub_eq (o := 468) (len := 7740) (bs := sigBytes r.w)
      (mem_raw r (raw_baseL r) _) (k := 4244) (n := 1024) (o' := 4712) (bs' := wotsRaw r 0)
      (by decide) rfl rfl)

/-- `b19`: to `26768`. -/
theorem s19 : Seg r b19Offset (fun m ↦ Facts r m ((4712, 1024, wotsRaw r 0) :: (8244, 1024, wotsRaw r 0) ::
      baseL r) ((.X9, r.off 4712) :: (.X10, r.off 8244) :: (.X21, ctr r 0) ::
      (.X23, r.off 15984) :: K0 r)) b20Offset
    (fun m ↦ Facts r m ((26768, 1024, wotsRaw r 0) :: baseL r) (K19 r)) := fun _ h ↦
  Eventually.mono (step_memcpy r hp hc hpre b19_in_code run_b19 rfl rfl rfl
    (a := 26768) (b := 8244) (n := 1024) rfl rfl rfl (by decide) (by decide) (by decide)
    h.dropK.dropK trivial (by facts_side) (by facts_side) (Lnew := []) (fun _ _ ↦ trivial)
    (Knew := [(.X24, r.off 8244)]) (fun _ hm' ↦ ⟨reg_ptr r hm' (a := 8244) rfl, trivial⟩)
    (by facts_side) (by facts_side) (bs := wotsRaw r 0) (by simp))
    fun _ ⟨hpc, h'⟩ ↦ ⟨hpc, h'.drop1.drop1⟩

/-- `b20`: layer 0's path to `15984`, the values to `24720`, X25 the raw signature. -/
theorem s20 : Seg r b20Offset (fun m ↦ Facts r m ((26768, 1024, wotsRaw r 0) :: baseL r) (K19 r)) b21Offset
    (fun m ↦ Facts r m ((24720, 1024, wotsRaw r 0) :: (15984, 128, pathRaw r 0) :: baseL r)
      ((.X25, r.off 468) :: K19 r)) := fun _ h ↦
  Eventually.mono (step_memcpy r hp hc hpre b20_in_code run_b20 rfl rfl rfl
    (a := 24720) (b := 26768) (n := 1024) rfl rfl rfl (by decide) (by decide) (by decide)
    h trivial (by facts_side) (by simp only [K19]; facts_side)
    (Lnew := [(15984, 128, pathRaw r 0)])
    (fun _ hm' ↦ pathL r h (mem_raw r (raw_baseL r) _) hm' (l := 0) (by decide) (by decide)
      (by decide) (by decide +kernel))
    (Knew := [(.X25, r.off 468)]) (fun _ hm' ↦ ⟨reg_ptr r hm' (a := 468) rfl, trivial⟩)
    (by facts_side) (by simp only [K19]; facts_side) (bs := wotsRaw r 0) (by simp))
    fun _ ⟨hpc, h'⟩ ↦ ⟨hpc, h'.drop2⟩

/-- **A copy of 1024 bytes `W`** from `b` to `a` by a straight block then `memcpy`, keeping the
other facts `L` and the registers `K` (`b21 .. b24`, `b29 .. b32`, `b37 .. b39`). -/
theorem s_copy {ds : List Directive} {j : Nat} (hk : ds.IsInfixAt Sphincs.SphincsVerify.code j)
    {S' : SState} (hx : exec ds (fs []) = some (S', .call NativeRustcArm.Common.Memcpy.entryLabel))
    (hw : Run.frameWrites S' = true) (hsp : S'.sp = .ptr 0 0)
    (h29 : S'.reg .X29 = some (.ptr 0 29280)) {a b : Nat}
    (h0 : S'.reg .X0 = some (.ptr 0 a)) (h1 : S'.reg .X1 = some (.ptr 0 b))
    (h2 : S'.reg .X2 = some (.lit 1024)) (ha : a + 1024 ≤ 29280) (hb : b + 1024 ≤ 29376)
    (hab : a + 1024 ≤ b ∨ b + 1024 ≤ a) (W : List UInt8) (L : List (Nat × Nat × List UInt8))
    (K : List (XReg × BitVec 64)) (hLb : noW S' ((b, 1024, W) :: L) = true)
    (hKb : keptK (fs []) S' K = true) (hLc : disj ((b, 1024, W) :: L) a 1024 = true)
    (hKc : savedK K = true) :
    Seg r j (fun m ↦ Facts r m ((b, 1024, W) :: L) K) (j + ds.length)
      (fun m ↦ Facts r m ((a, 1024, W) :: L) K) := fun _ h ↦
  Eventually.mono (step_memcpy r hp hc hpre hk hx hw hsp h29 h0 h1 h2 ha hb hab h trivial hLb hKb
    (Lnew := []) (fun _ _ ↦ trivial) (Knew := []) (fun _ _ ↦ trivial) hLc hKc (bs := W)
    List.mem_cons_self) fun _ ⟨hpc, h'⟩ ↦ ⟨hpc, h'.drop1⟩

/-- **Layer 0 of the tail**, `b16 .. b24`. -/
theorem layer0 : Seg r b16Offset r.AtParse16 b25Offset (fun m ↦ Facts r m (L25 r) (K25 r)) := fun m h ↦
  ((((((((s16 r hp hc hpre).trans (s17 r hp hpre)).trans (s18 r hp hpre)).trans
    (s19 r hp hc hpre)).trans (s20 r hp hc hpre)).trans
    (s_copy r hp hc hpre b21_in_code run_b21 rfl rfl rfl (a := 23696) (b := 24720) rfl rfl rfl
      (by decide) (by decide) (by decide) (wotsRaw r 0) ((15984, 128, pathRaw r 0) :: baseL r)
      (K21 r) (by facts_side) (by simp only [K21, K19]; facts_side) (by facts_side)
      (by simp only [K21, K19]; facts_side))).trans
    (s_copy r hp hc hpre b22_in_code run_b22 rfl rfl rfl (a := 22672) (b := 23696) rfl rfl rfl
      (by decide) (by decide) (by decide) (wotsRaw r 0) ((15984, 128, pathRaw r 0) :: baseL r)
      (K21 r) (by facts_side) (by simp only [K21, K19]; facts_side) (by facts_side)
      (by simp only [K21, K19]; facts_side))).trans
    (s_copy r hp hc hpre b23_in_code run_b23 rfl rfl rfl (a := 25744) (b := 22672) rfl rfl rfl
      (by decide) (by decide) (by decide) (wotsRaw r 0) ((15984, 128, pathRaw r 0) :: baseL r)
      (K21 r) (by facts_side) (by simp only [K21, K19]; facts_side) (by facts_side)
      (by simp only [K21, K19]; facts_side))).trans
    (s_copy r hp hc hpre b24_in_code run_b24 rfl rfl rfl (a := 21648) (b := 25744) rfl rfl rfl
      (by decide) (by decide) (by decide) (wotsRaw r 0) ((15984, 128, pathRaw r 0) :: baseL r)
      (K21 r) (by facts_side) (by simp only [K21, K19]; facts_side) (by facts_side)
      (by simp only [K21, K19]; facts_side)) m (facts_entry r h)

end

end NativeRustcArm.SphincsVerifyProof.ParseTail
