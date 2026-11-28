module

public import NativeRustcVmArm.KeccakGkr.VerifyLayer.FrontKeep
public import Mathlib.Data.List.GetD

/-!
# `verify_layer`'s front: shared steps

Sums of `E` by limbs (`ew_mk_add`, `xs_split2`, `xs_split4`), the `csel`s that keep a term when a
mask's bit is set (`selSym`, `selSym'`), an `eor` (`eorSym`), the read-only and argument regions
as numbers (`PGeo`), their words in a front's state (`mask_word`, `mu_word`, `w_word`,
`rc_word`), and a block of the front writing nothing (`fb_run`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVm.Layout (Same)
open NativeRustcVm.Transcript (tstateBytes TStateAt DecArea)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt claimBytes)

public section

/-! ## Sums by limbs -/

theorem ew_mk_add (a b c d : UInt64) : (⟨a, b⟩ : EW) + ⟨c, d⟩ = ⟨a ^^^ c, b ^^^ d⟩ := rfl

theorem ew_add_assoc' (x y z : EW) : x + y + z = x + (y + z) := by
  show (⟨(x.c0 ^^^ y.c0) ^^^ z.c0, (x.c1 ^^^ y.c1) ^^^ z.c1⟩ : EW) =
    ⟨x.c0 ^^^ (y.c0 ^^^ z.c0), x.c1 ^^^ (y.c1 ^^^ z.c1)⟩
  rw [UInt64.xor_assoc, UInt64.xor_assoc]

instance ewAddAssoc : Std.Associative (α := EW) (· + ·) := ⟨ew_add_assoc'⟩
instance ewAddComm : Std.Commutative (α := EW) (· + ·) := ⟨ew_add_comm'⟩

theorem sel_c0 (b : Bool) (x : EW) : (sel b x).c0 = if b then x.c0 else 0 := by
  cases b <;> rfl

theorem sel_c1 (b : Bool) (x : EW) : (sel b x).c1 = if b then x.c1 else 0 := by
  cases b <;> rfl

/-- A sum in two interleaved halves. -/
theorem xs_split2 (f : Nat → EW) :
    ∀ p, xs f (2 * p) = xs (fun i ↦ f (2 * i)) p + xs (fun i ↦ f (2 * i + 1)) p
  | 0 => (ew_add_zero' 0).symm
  | p + 1 => by
    rw [show 2 * (p + 1) = 2 * p + 1 + 1 by omega, xs_succ, xs_succ, xs_succ, xs_succ,
      xs_split2 f p]
    ac_rfl

/-- A sum in four interleaved quarters. -/
theorem xs_split4 (f : Nat → EW) (q : Nat) :
    xs f (4 * q) = xs (fun i ↦ f (4 * i)) q + xs (fun i ↦ f (4 * i + 1)) q +
      (xs (fun i ↦ f (4 * i + 2)) q + xs (fun i ↦ f (4 * i + 3)) q) := by
  have h := xs_split2 f (2 * q)
  rw [xs_split2 (fun i ↦ f (2 * i)) q, xs_split2 (fun i ↦ f (2 * i + 1)) q] at h
  rw [show 4 * q = 2 * (2 * q) by omega, h]
  simp only [show ∀ i, 2 * (2 * i) = 4 * i from fun i ↦ by omega,
    show ∀ i, 2 * (2 * i + 1) = 4 * i + 2 from fun i ↦ by omega,
    show ∀ i, 4 * i + 2 + 1 = 4 * i + 3 from fun i ↦ by omega]
  ac_rfl

/-! ## Terms the code keeps -/

theorem and_apply (x y : BitVec 64) : BinOp.apply .and .W64 x y = x &&& y := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64]

/-- A kept register. -/
theorem kg {L : List XReg} {m m' : MachineData} (h : Bus.KeepRegs L m m') (r : XReg)
    (hr : r ∈ L := by simp) : m'.regs.getXReg r = m.regs.getXReg r := h r hr

theorem eor_apply (x y : BitVec 64) : BinOp.apply .eor .W64 x y = x ^^^ y := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64]

section
variable [Labels] {env : Env}

/-- `csel x, xzr, v, eq` after `tst w, 1 << c`: `v` when bit `c` of `w` is set. -/
theorem selSym {A B V : Sym} {w x : UInt64} {c : Nat} (hc : c < 64)
    (hA : A.eval env = w.toBitVec) (hB : (B.eval env).toNat = 2 ^ c)
    (hV : V.eval env = x.toBitVec) :
    (Sym.ite (.cmp .eq .W64 (.bin .and .W64 A B) (.lit 0)) (.lit 0) V).eval env =
      (if testBitW w c then x else 0).toBitVec := by
  rw [ev_ite, sb_cmp, ev_bin, hA, ev_lit, tst_eq w hc _ hB]
  cases testBitW w c
  · rfl
  · exact hV

/-- `csel x, xzr, v, eq` after `tst 1 << c, w`. -/
theorem selSym' {A B V : Sym} {w x : UInt64} {c : Nat} (hc : c < 64)
    (hA : (A.eval env).toNat = 2 ^ c) (hB : B.eval env = w.toBitVec)
    (hV : V.eval env = x.toBitVec) :
    (Sym.ite (.cmp .eq .W64 (.bin .and .W64 A B) (.lit 0)) (.lit 0) V).eval env =
      (if testBitW w c then x else 0).toBitVec := by
  rw [ev_ite, sb_cmp, ev_bin, hB, and_apply, BitVec.and_comm, ← and_apply, ev_lit,
    tst_eq w hc _ hA]
  cases testBitW w c
  · rfl
  · exact hV

/-- `eor`. -/
theorem eorSym {A B : Sym} {x y : UInt64} (hA : A.eval env = x.toBitVec)
    (hB : B.eval env = y.toBitVec) : (Sym.bin .eor .W64 A B).eval env = (x ^^^ y).toBitVec := by
  rw [ev_bin, hA, hB, eor_apply, UInt64.toBitVec_xor]

/-- A register's value from its symbolic one. -/
theorem reg_val {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState} {r : XReg}
    {v : Sym} {x : UInt64} (hm : Match (Env.ofMachine m rs) S m') (h : S.reg r = some v)
    (hv : v.eval (Env.ofMachine m rs) = x.toBitVec) : m'.regs.getXReg r = x :=
  UInt64.toBitVec_inj.mp ((hm.regs r v h).trans hv)

/-- A register's atom. -/
theorem ev_regU (m : MachineData) (rs : List (BitVec 64 × Nat)) (r : XReg) :
    (Sym.reg r).eval (Env.ofMachine m rs) = (m.regs.getXReg r).toBitVec := by
  rw [ev_reg]; rfl

/-- A word of a region, loaded. -/
theorem ev_loadW {m : MachineData} {rs : List (BitVec 64 × Nat)} {r o : Nat} {v : UInt64}
    (h : NativeRustcVm.WordAt m.dmem ((Env.ofMachine m rs).base r + BitVec.ofNat 64 o) v) :
    (Sym.load r o 8).eval (Env.ofMachine m rs) = v.toBitVec := by
  rw [ev_load]; exact Ring.load_word h

/-- A word of a region at a known base, loaded. -/
theorem ev_loadB {m : MachineData} {rs : List (BitVec 64 × Nat)} {r o : Nat} {b : BitVec 64}
    {v : UInt64} (hb : (Env.ofMachine m rs).base r = b)
    (h : NativeRustcVm.WordAt m.dmem (b + BitVec.ofNat 64 o) v) :
    (Sym.load r o 8).eval (Env.ofMachine m rs) = v.toBitVec := by
  rw [ev_load]; exact Ring.load_word (by rw [hb]; exact h)

/-- A register's atom as a number. -/
theorem regN {m : MachineData} {rs : List (BitVec 64 × Nat)} (r : XReg) {n : Nat}
    (h : (m.regs.getXReg r).toNat = n) : ((Sym.reg r).eval (Env.ofMachine m rs)).toNat = n := by
  rw [ev_regU]; exact h

/-- A literal as a number. -/
theorem litN (n : Nat) (h : n < 2 ^ 64 := by decide) : ((Sym.lit n).eval env).toNat = n := by
  rw [ev_lit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- A register's atom as a vector. -/
theorem regB {m : MachineData} {rs : List (BitVec 64 × Nat)} (r : XReg) {x : BitVec 64}
    (h : (m.regs.getXReg r).toBitVec = x) : (Sym.reg r).eval (Env.ofMachine m rs) = x := by
  rw [ev_regU]; exact h

/-- A word of region `0` of two, loaded. -/
theorem ld0 {m : MachineData} {b0 b1 : BitVec 64} {n0 n1 o : Nat} {v : UInt64}
    (h : NativeRustcVm.WordAt m.dmem (b0 + BitVec.ofNat 64 o) v) :
    (Sym.load 0 o 8).eval (Env.ofMachine m [(b0, n0), (b1, n1)]) = v.toBitVec :=
  ev_loadB rfl h

/-- A word of region `1` of two, loaded. -/
theorem ld1 {m : MachineData} {b0 b1 : BitVec 64} {n0 n1 o : Nat} {v : UInt64}
    (h : NativeRustcVm.WordAt m.dmem (b1 + BitVec.ofNat 64 o) v) :
    (Sym.load 1 o 8).eval (Env.ofMachine m [(b0, n0), (b1, n1)]) = v.toBitVec :=
  ev_loadB rfl h

/-- A word of the only region, loaded. -/
theorem ldF {m : MachineData} {b0 : BitVec 64} {n0 o : Nat} {v : UInt64}
    (h : NativeRustcVm.WordAt m.dmem (b0 + BitVec.ofNat 64 o) v) :
    (Sym.load 0 o 8).eval (Env.ofMachine m [(b0, n0)]) = v.toBitVec :=
  ev_loadB rfl h

/-- `x + (y << s)`. -/
theorem addShl {A B : Sym} {x : BitVec 64} {y s : Nat} (hA : A.eval env = x)
    (hB : (B.eval env).toNat = y) :
    (Sym.bin .add .W64 A (.un (.shift .LSL s) .W64 B)).eval env =
      x + BitVec.ofNat 64 (2 ^ s * y) := by
  rw [ev_bin, ev_un, hA]
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.apply, UnOp.apply, Sym.low_W64, Sym.ext_W64, shiftW, BitVec.toNat_add,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hB, BitVec.toNat_ofNat]
  rw [Nat.mul_comm (2 ^ s) y]

/-- `x - y` without borrow. -/
theorem subSym {A B : Sym} {x y : Nat} (hA : (A.eval env).toNat = x)
    (hB : (B.eval env).toNat = y) (h : y ≤ x) :
    ((Sym.bin .sub .W64 A B).eval env).toNat = x - y := by
  rw [ev_bin, sub_toNat, hA, hB]
  have := hA ▸ (A.eval env).isLt
  omega

end

/-! ## Addresses -/

theorem addr_eq {x : BitVec 64} {a b : Nat} (h : a = b) :
    x + BitVec.ofNat 64 a = x + BitVec.ofNat 64 b := by rw [h]

theorem mapped_sub {d0 d : DataMem} (hk : Kept d0 d) {a : BitVec 64} {n : Nat}
    (h : NativeRustcVm.Mapped d0 a n) {o k : Nat} (hon : o + k ≤ n) :
    Mapped d (a + BitVec.ofNat 64 o) k := fun i hi ↦ by
  rw [NativeRustcVm.addr_add_add]; exact hk _ (h _ (by omega))

/-- **The read-only and argument regions as numbers.** -/
structure PGeo [Labels] (m0 : MachineData) : Prop where
  pn : projectAddr.toNat + 128 ≤ 2 ^ 64
  rn : rcAddr.toNat + 192 ≤ 2 ^ 64
  pc : (cA m0).toNat + 768 ≤ projectAddr.toNat ∨ projectAddr.toNat + 128 ≤ (cA m0).toNat
  rs : rcAddr.toNat + 192 ≤ m0.regs.SP.toNat - 3648 ∨ m0.regs.SP.toNat ≤ rcAddr.toNat
  pm : NativeRustcVm.Mapped m0.dmem projectAddr 128
  rm : NativeRustcVm.Mapped m0.dmem rcAddr 192
  cm : NativeRustcVm.Mapped m0.dmem (cA m0) 768
  sm : NativeRustcVm.Mapped m0.dmem (sA m0) 205824

section
variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

theorem pgeo_of (h : VerifyLayerPre a s c m0) : PGeo m0 := by
  have g := geo_of h
  have hA := pre_areas h
  have hpr : projectRegion ∈ [a.region, rcRegion, projectRegion, rhoRegion] := by simp
  have hrr : rcRegion ∈ [a.region, rcRegion, projectRegion, rhoRegion] := by simp
  have hp := hA.1 _ (List.mem_append.mpr (.inr hpr))
  have hr := hA.1 _ (List.mem_append.mpr (.inr hrr))
  have hc := hA.1 ⟨cA m0, claimBytes⟩ (by simp)
  have hs := hA.1 ⟨sA m0, NativeRustcVm.KeccakGkr.scratchBytes⟩ (by simp)
  have hcp := hA.2.2 ⟨cA m0, claimBytes⟩ (by simp) _ hpr
  have hrs := hA.2.2 _ List.mem_cons_self _ hrr
  have := g.hN
  have hspn : m0.regs.SP.toNat = m0.regs.SP.toBitVec.toNat := rfl
  have hsb : (stackBelow m0 3648).toNat = m0.regs.SP.toNat - 3648 :=
    NativeRustcVm.toNat_sub_ofNat (by omega)
  unfold Apart at hcp hrs
  simp only [stackRegion, stack_eq, claimBytes, projectRegion, rcRegion] at hp hr hcp hrs
  rw [hsb] at hrs
  exact ⟨hp.2, hr.2, hcp, by omega, hp.1, hr.1, hc.1, hs.1⟩

/-- `RMFE_PROJECT`'s word `i`. -/
theorem mask_word {d : DataMem} (hp : NativeRustcVm.WordsAt d projectAddr rmfeProjectW.toList)
    {i : Nat} (hi : i < 16) :
    NativeRustcVm.WordAt d (projectAddr + BitVec.ofNat 64 (8 * i)) (rmfeProjectW.getD i 0) := by
  have hi' : i < rmfeProjectW.toList.length := by
    rw [Array.length_toList, rmfeProjectW_size]; exact hi
  have := hp.getElem hi'
  rwa [← List.getD_eq_getElem _ 0 hi', ← getD_toList] at this

/-- `KECCAK_RC`'s word `i`. -/
theorem rc_word {d : DataMem} (hp : NativeRustcVm.WordsAt d rcAddr LeanVM.Parameters.keccakRC)
    {i : Nat} (hi : i < 24) :
    NativeRustcVm.WordAt d (rcAddr + BitVec.ofNat 64 (8 * i)) (keccakRCW.getD i 0) := by
  have hl : LeanVM.Parameters.keccakRC.length = 24 := by decide
  have hi' : i < LeanVM.Parameters.keccakRC.length := by rw [hl]; exact hi
  have := hp.getElem hi'
  have e : keccakRCW.getD i 0 = LeanVM.Parameters.keccakRC[i] := by
    simp [keccakRCW, Array.getD_eq_getD_getElem?, hi']
  rw [e]; exact this

omit [Labels] in
/-- An element of `E`, word by word. -/
theorem ew_words {d : DataMem} {p : BitVec 64} {xs : List EW} (h : NativeRustcVm.EWsAt d p xs)
    {i : Nat} (hi : i < xs.length) :
    NativeRustcVm.WordAt d (p + BitVec.ofNat 64 (16 * i)) (xs.getD i 0).c0 ∧
      NativeRustcVm.WordAt d (p + BitVec.ofNat 64 (16 * i + 8)) (xs.getD i 0).c1 := by
  have := h.getElem hi
  rw [NativeRustcVm.ewAt_iff, NativeRustcVm.addr_add_add] at this
  rw [List.getD_eq_getElem _ _ hi]
  exact this

omit [Labels] in
/-- The claim's instance weights' entry `i`, word by word. -/
theorem mu_word {d : DataMem} (hc : ClaimAt d (cA m0) c) {i : Nat} (hi : i < c.mu.size) :
    NativeRustcVm.WordAt d (cA m0 + BitVec.ofNat 64 (24 + 16 * i)) (c.mu.getD i 0).c0 ∧
      NativeRustcVm.WordAt d (cA m0 + BitVec.ofNat 64 (24 + 16 * i + 8)) (c.mu.getD i 0).c1 := by
  have he : NativeRustcVm.EWsAt d (cA m0 + BitVec.ofNat 64 24) c.mu.toList := by
    have := hc.2.1.2.2
    rwa [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, NativeRustcVm.KeccakGkr.off,
      NativeRustcVm.KeccakGkr.muOff, NativeRustcVm.addr_add_add] at this
  have := ew_words he (i := i) (by rw [Array.length_toList]; exact hi)
  rw [NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add, ← getD_toList] at this
  rw [show 24 + 16 * i + 8 = 24 + (16 * i + 8) by omega]
  exact this

omit [Labels] in
/-- The claim's instance weights' count. -/
theorem mu_len {d : DataMem} (hc : ClaimAt d (cA m0) c) :
    NativeRustcVm.WordAt d (cA m0 + BitVec.ofNat 64 16) c.mu.size.toUInt64 ∧ c.mu.size ≤ 16 := by
  obtain ⟨h1, h2, -⟩ := hc.2.1
  rw [Array.length_toList] at h1 h2
  exact ⟨h2, h1⟩

omit [Labels] in
/-- The claim's bit weight `z`, word by word. -/
theorem w_word {d : DataMem} (hw : WeightsAt d (sA m0 + BitVec.ofNat 64 25600) c) {z : Nat}
    (hz : z < 1600) :
    NativeRustcVm.WordAt d (sA m0 + BitVec.ofNat 64 (25600 + 16 * z)) (c.weights.getD z 0).c0 ∧
      NativeRustcVm.WordAt d (sA m0 + BitVec.ofNat 64 (25600 + 16 * z + 8))
        (c.weights.getD z 0).c1 := by
  have := ew_words hw.2 (i := z) (by rw [Array.length_toList, hw.1]; exact hz)
  rw [NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add, ← getD_toList] at this
  rw [show 25600 + 16 * z + 8 = 25600 + (16 * z + 8) by omega]
  exact this

end

/-! ## Changes below the frame -/

section
variable {m0 : MachineData}

/-- The `1616` bytes below the frame, where the front's callees keep their stacks. -/
@[expose] def Bel (m0 : MachineData) (q : BitVec 64) : Prop := InRange (base m0 3648) 1616 q

/-- A callee's stack below the frame. -/
theorem bel_of (g : Geo m0) {m : MachineData} (hsp : m.regs.SP.toBitVec = base m0 2032)
    {N' : Nat} (hN : N' ≤ 1616) {q : BitVec 64} (h : InRange (stackBelow m N') N' q) :
    Bel m0 q := by
  have := g.hN; have := Geo.sp_lt m0
  have hst := g.stk hsp hN
  have hb : (base m0 3648).toNat = m0.regs.SP.toNat - 3648 := base_toNat (by omega)
  unfold Bel
  rw [Sym.inRange_iff (by rw [hst]; omega), hst] at h
  rw [Sym.inRange_iff (by rw [hb]; omega), hb]
  omega

/-- **A range apart from the bytes below the frame** stays the same. -/
theorem same_bel (g : Geo m0) {d d' : DataMem} (hs : SameOutside d d' (Bel m0)) {x : BitVec 64}
    {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64)
    (h : m0.regs.SP.toNat - 2032 ≤ x.toNat ∨ x.toNat + n ≤ m0.regs.SP.toNat - 3648) :
    Same d d' x n := by
  have := g.hN; have := Geo.sp_lt m0
  have hb : (base m0 3648).toNat = m0.regs.SP.toNat - 3648 := base_toNat (by omega)
  refine NativeRustcVm.Layout.Same.of_sameOutside hs fun j hj hq ↦ ?_
  exact notIn (by rw [hb]; omega) (by omega) (by rw [hb]; omega) hq

/-- The frame's bytes `o` to `o + n` stay the same. -/
theorem loc_bel (g : Geo m0) {d d' : DataMem} (hs : SameOutside d d' (Bel m0)) {o n : Nat}
    (hon : o + n ≤ 2032) : Same d d' (loc m0 o) n := by
  have := g.hN; have := Geo.sp_lt m0
  exact same_bel g hs (by rw [g.fa (by omega)]; omega) (by rw [g.fa (by omega)]; omega)

/-- The scratch's bytes `o` to `o + n` stay the same. -/
theorem scr_bel (g : Geo m0) {d d' : DataMem} (hs : SameOutside d d' (Bel m0)) {o n : Nat}
    (ho : o < 205824) (hon : o + n ≤ 205824) : Same d d' (sA m0 + BitVec.ofNat 64 o) n := by
  have := g.hs; have := g.hss; have := g.hN
  exact same_bel g hs (by rw [g.sa ho]; omega) (by rw [g.sa ho]; omega)

/-- The claim's bytes stay the same. -/
theorem claim_bel (g : Geo m0) {d d' : DataMem} (hs : SameOutside d d' (Bel m0)) :
    Same d d' (cA m0) 768 := by
  have := g.hc; have := g.hcs; have := g.hN
  exact same_bel g hs (by omega) (by omega)

/-- **The `TState`** kept by changes below the frame. -/
theorem ts_bel [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW}
    (h : VerifyLayerPre a s c m0) {d d' : DataMem} (hk : Kept d d')
    (hs : SameOutside d d' (Bel m0)) {s' : TState} (ht : TStateAt d (tA m0) a s') :
    TStateAt d' (tA m0) a s' := by
  have g := geo_of h
  obtain ⟨hw, hws, -, -⟩ := dec_geo h
  refine NativeRustcVm.Transcript.TStateAt.frame ht hk (fun q hq ↦ ?_) hs
  have := g.hN; have := g.ht; have := g.hts; have := Geo.sp_lt m0
  have hb : (base m0 3648).toNat = m0.regs.SP.toNat - 3648 := base_toNat (by omega)
  unfold Bel at hq
  rw [Sym.inRange_iff (by rw [hb]; omega), hb] at hq
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' : InRange (tA m0) 760 q := h
    rw [Sym.inRange_iff (by omega)] at h'
    omega
  · have h' : InRange a.words (8 * a.len) q := h
    rw [Sym.inRange_iff hw] at h'
    omega

end

/-! ## Blocks of the front -/

section
variable [Host] {m0 : MachineData}

/-- **A block of the front writing nothing**, in any environment over the state's memory. -/
theorem fb_run {env : Env} {ds : List Directive} {j : Nat} {S S' : SState} {x : Exit}
    {st : MachineState} {R : MachineState → Prop} (hb : FB m0 st.data)
    (hk : ds.IsInfixAt Host.prog j) (hx : exec ds S = some (S', x)) (hwf : env.WF)
    (hd : st.data.dmem = env.mem0) (hpc : st.pc = Host.addrOf j) (hm : Match env S st.data)
    (hmem : S'.mem = []) (hsp : S'.sp = S.sp)
    (cont : ∀ st', FB m0 st'.data → st'.data.dmem = st.data.dmem → Match env S' st'.data →
      PcOk env x (Host.addrOf (j + ds.length)) st' → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st :=
  exec_at hk hx hwf hpc hm fun st' hm' hpc' ↦
    cont st' (Fr.ofBlock hb hm hm' hwf hd hmem hsp fun r hr ↦ by cases hr)
      ((hm'.dmem_eq hwf hmem).trans hd.symm) hm' hpc'

end

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
