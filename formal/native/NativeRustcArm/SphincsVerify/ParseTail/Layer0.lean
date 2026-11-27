module

public import NativeRustcArm.Code.Common.Memcpy.Names

public import NativeRustcArm.SphincsVerify.ParseTail.State

/-!
# The parse's tail, layer 0 (`b7 .. b15`)

`b7` zeroes the paths' last 288 bytes (`8352..8640`) and sets X25 = `8224`; `b8` loads layer 0's
counter (`ctr r 0`, in X23) and the copy loop `b9` copies its chain values to `484`; `b10 .. b15`
move them by `memcpy` to `19008`, `16960`, `15936`, `14912`, `17984` and `13888`, `b10` setting
X26 = `484` and `b11` storing layer 0's path at `8224`.
-/

namespace NativeRustcArm.SphincsVerifyProof.ParseTail

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify

set_option Elab.async false

@[expose] public section

/-- The facts after layer 0, at `b16`. -/
def L16 (r : Run) : List (Nat × Nat × List UInt8) :=
  (13888, 1024, wotsRaw r 0) :: (8224, 128, pathRaw r 0) :: baseL r

/-- The registers from `b10` on (layer 0's: `K16`). -/
def K16 (r : Run) : List (XReg × BitVec 64) :=
  (.X26, r.off 484) :: (.X23, ctr r 0) :: (.X25, r.off 8224) :: K0 r

end

public section

variable (r : Run)

variable [ElfHost] (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees) (hpre : r.Pre)
include hp hc hpre

/-- `b7`: the paths' last 288 bytes zeroed. -/
theorem s7 : Seg r b7Offset (fun m ↦ Facts r m (baseL r) (K0 r)) b8Offset
    (fun m ↦ Facts r m (baseL r) ((.X25, r.off 8224) :: K0 r)) := fun _ h ↦
  step_memset r hp hc hpre b7_in_code run_b7 rfl rfl rfl (a := 8352) (n := 288) rfl rfl
    (by decide) h trivial (by facts_side) (by facts_side) (Knew := [(.X25, r.off 8224)])
    (fun _ hm' ↦ ⟨reg_ptr r hm' (a := 8224) rfl, trivial⟩) (by facts_side) (by facts_side)

omit hc in
/-- `b8`: layer 0's counter, the copy loop's registers. -/
theorem s8 : Seg r b8Offset (fun m ↦ Facts r m (baseL r) ((.X25, r.off 8224) :: K0 r)) b9Offset
    (fun m ↦ Facts r m (baseL r) ((.X8, BitVec.ofNat 64 0) :: (.X9, r.sigPtr + BitVec.ofNat 64 4244) ::
      (.X10, r.off 484) :: (.X23, ctr r 0) :: (.X25, r.off 8224) :: K0 r)) := fun m h ↦
  step_fall r hp hpre b8_in_code (by unfold b8; simp) run_b8 rfl rfl rfl h
    ⟨(h.reg (x := .X19) (v := r.sigPtr) (by simp [K0])).trans (by show _ = r.sigPtr + BitVec.ofInt 64 0; simp), trivial⟩
    (by facts_side) (by facts_side) (Lnew := []) (fun _ _ ↦ trivial)
    (Knew := [(.X8, BitVec.ofNat 64 0), (.X9, r.sigPtr + BitVec.ofNat 64 4244),
      (.X10, r.off 484), (.X23, ctr r 0)])
    (fun _ hm' ↦ ⟨reg_lit r hm' rfl, reg_ptr1 r hm' (a := 4244) rfl, reg_ptr r hm' (a := 484) rfl,
      reg_load1 r hm' rfl (by simp [slice, r.hsig, sigLayerOff])
        (Parse.bytesAt_sig_sub r hpre h.1.2.2.2.1 (s := 4240) (k := 4) (by decide)), trivial⟩)

omit hc in
/-- `b9`: the copy loop, layer 0's chain values to `484`. -/
theorem s9 : Seg r b9Offset (fun m ↦ Facts r m (baseL r) ((.X8, BitVec.ofNat 64 0) ::
      (.X9, r.sigPtr + BitVec.ofNat 64 4244) :: (.X10, r.off 484) :: (.X23, ctr r 0) ::
      (.X25, r.off 8224) :: K0 r)) b10Offset
    (fun m ↦ Facts r m ((484, 1024, wotsRaw r 0) :: baseL r)
      ((.X9, r.sigPtr + BitVec.ofNat 64 4244) :: (.X10, r.off 484) :: (.X23, ctr r 0) ::
        (.X25, r.off 8224) :: K0 r)) :=
  fun _ h ↦ copy_loop r hp hpre b9_in_code (by unfold b9; simp)
    (getElem?_of_infix b9_in_code rfl) run_b9 rfl (src := 4244) (by decide)
    (by facts_side) (by facts_side) (h.nil 484)

/-- `b10`: to `19008`, X26 = `484`. -/
theorem s10 : Seg r b10Offset (fun m ↦ Facts r m ((484, 1024, wotsRaw r 0) :: baseL r)
      ((.X9, r.sigPtr + BitVec.ofNat 64 4244) :: (.X10, r.off 484) :: (.X23, ctr r 0) ::
        (.X25, r.off 8224) :: K0 r)) b11Offset
    (fun m ↦ Facts r m ((19008, 1024, wotsRaw r 0) :: baseL r) (K16 r)) := fun _ h ↦
  Eventually.mono_elf (step_memcpy r hp hc hpre b10_in_code run_b10 rfl rfl rfl
    (a := 19008) (b := 484) (n := 1024) rfl rfl rfl (by decide) (by decide) (by decide)
    h.dropK.dropK trivial (by facts_side) (by facts_side) (Lnew := []) (fun _ _ ↦ trivial)
    (Knew := [(.X26, r.off 484)]) (fun _ hm' ↦ ⟨reg_ptr r hm' (a := 484) rfl, trivial⟩)
    (by facts_side) (by facts_side) (bs := wotsRaw r 0) (by simp))
    fun _ ⟨hpc, h'⟩ ↦ ⟨hpc, h'.drop1⟩

/-- `b11`: layer 0's path to `8224`, the values to `16960`. -/
theorem s11 : Seg r b11Offset (fun m ↦ Facts r m ((19008, 1024, wotsRaw r 0) :: baseL r) (K16 r)) b12Offset
    (fun m ↦ Facts r m ((16960, 1024, wotsRaw r 0) :: (8224, 128, pathRaw r 0) :: baseL r)
      (K16 r)) := fun m h ↦
  Eventually.mono_elf (step_memcpy r hp hc hpre b11_in_code run_b11 rfl rfl rfl
    (a := 16960) (b := 19008) (n := 1024) rfl rfl rfl (by decide) (by decide) (by decide)
    h ⟨(h.reg (x := .X19) (v := r.sigPtr) (by simp [K16, K0])).trans (by show _ = r.sigPtr + BitVec.ofInt 64 0; simp), trivial⟩
    (by facts_side) (by simp only [K16]; facts_side)
    (Lnew := [(8224, 128, pathRaw r 0)])
    (fun _ hm' ↦ pathL r hpre h.1 hm' (l := 0) (by decide) (by decide) (by decide) (by decide +kernel))
    (Knew := []) (fun _ _ ↦ trivial)
    (by facts_side) (by simp only [K16]; facts_side) (bs := wotsRaw r 0) (by simp))
    fun _ ⟨hpc, h'⟩ ↦ ⟨hpc, h'.drop2⟩

/-- **A copy of 1024 bytes `W`** from `b` to `a` by a straight block then `memcpy`, keeping the
other facts `L` and the registers `K` (`b12 .. b15`, `b20 .. b23`, `b28 .. b30`). -/
theorem s_copy {ds : List Directive} {j : Nat} (hk : ds.IsInfixAt Sphincs.SphincsVerify.code j)
    {S' : SState} (hx : exec ds (fs []) = some (S', .call NativeRustcArm.Common.Memcpy.entryLabel))
    (hw : Run.frameWrites S' = true) (hsp : S'.sp = .ptr 0 0)
    (h29 : S'.reg .X29 = some (.ptr 0 21520)) {a b : Nat}
    (h0 : S'.reg .X0 = some (.ptr 0 a)) (h1 : S'.reg .X1 = some (.ptr 0 b))
    (h2 : S'.reg .X2 = some (.lit 1024)) (ha : a + 1024 ≤ 21520) (hb : b + 1024 ≤ 21616)
    (hab : a + 1024 ≤ b ∨ b + 1024 ≤ a) (W : List UInt8) (L : List (Nat × Nat × List UInt8))
    (K : List (XReg × BitVec 64)) (hLb : noW S' ((b, 1024, W) :: L) = true)
    (hKb : keptK (fs []) S' K = true) (hLc : disj ((b, 1024, W) :: L) a 1024 = true)
    (hKc : savedK K = true) :
    Seg r j (fun m ↦ Facts r m ((b, 1024, W) :: L) K) (j + ds.length)
      (fun m ↦ Facts r m ((a, 1024, W) :: L) K) := fun _ h ↦
  Eventually.mono_elf (step_memcpy r hp hc hpre hk hx hw hsp h29 h0 h1 h2 ha hb hab h trivial hLb hKb
    (Lnew := []) (fun _ _ ↦ trivial) (Knew := []) (fun _ _ ↦ trivial) hLc hKc (bs := W)
    List.mem_cons_self) fun _ ⟨hpc, h'⟩ ↦ ⟨hpc, h'.drop1⟩

/-- **Layer 0 of the tail**, `b7 .. b15`. -/
theorem layer0 : Seg r b7Offset r.AtParse7 b16Offset (fun m ↦ Facts r m (L16 r) (K16 r)) := fun m h ↦
  ((((((((s7 r hp hc hpre).trans (s8 r hp hpre)).trans (s9 r hp hpre)).trans
    (s10 r hp hc hpre)).trans (s11 r hp hc hpre)).trans
    (s_copy r hp hc hpre b12_in_code run_b12 rfl rfl rfl (a := 15936) (b := 16960) rfl rfl rfl
      (by decide) (by decide) (by decide) (wotsRaw r 0) ((8224, 128, pathRaw r 0) :: baseL r)
      (K16 r) (by facts_side) (by simp only [K16]; facts_side) (by facts_side)
      (by simp only [K16]; facts_side))).trans
    (s_copy r hp hc hpre b13_in_code run_b13 rfl rfl rfl (a := 14912) (b := 15936) rfl rfl rfl
      (by decide) (by decide) (by decide) (wotsRaw r 0) ((8224, 128, pathRaw r 0) :: baseL r)
      (K16 r) (by facts_side) (by simp only [K16]; facts_side) (by facts_side)
      (by simp only [K16]; facts_side))).trans
    (s_copy r hp hc hpre b14_in_code run_b14 rfl rfl rfl (a := 17984) (b := 14912) rfl rfl rfl
      (by decide) (by decide) (by decide) (wotsRaw r 0) ((8224, 128, pathRaw r 0) :: baseL r)
      (K16 r) (by facts_side) (by simp only [K16]; facts_side) (by facts_side)
      (by simp only [K16]; facts_side))).trans
    (s_copy r hp hc hpre b15_in_code run_b15 rfl rfl rfl (a := 13888) (b := 17984) rfl rfl rfl
      (by decide) (by decide) (by decide) (wotsRaw r 0) ((8224, 128, pathRaw r 0) :: baseL r)
      (K16 r) (by facts_side) (by simp only [K16]; facts_side) (by facts_side)
      (by simp only [K16]; facts_side)) m (facts_entry r h)

end

end NativeRustcArm.SphincsVerifyProof.ParseTail
