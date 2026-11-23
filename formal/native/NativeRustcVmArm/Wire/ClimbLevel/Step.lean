module

public import NativeRustcVmArm.Wire.ClimbLevel.State

/-!
# `climb_level`'s steps

What a block writing the frame and one node keeps: the frame (`Geo.frm_block`), the memory
outside `Keep` (`Geo.written_keep`); the words of a node it writes (`node_write`); the
registers the set-up fixed (`Fix.keep`); the slots' words as the executor loads them
(`load_rdr`, `load_nxt`).
-/

namespace NativeRustcVmArm.Wire.ClimbLevel

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.ClimbLevel
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

public section

variable [Labels] {m0 : MachineData} {bp : BitVec 64} {B : List UInt8}

theorem Geo.sb_keep (G : Geo m0 bp B) {i t : Nat} (hi : i < 256) (ht : t < 40) (lp : Nat) :
    Keep m0 i lp (sb m0 i + BitVec.ofNat 64 t) := by
  have := G.sbNw
  refine .inr (.inr (.inl ?_))
  unfold nodesBytes
  rw [Sym.inRange_iff (by rw [toNat_off (by omega)]; omega), toNat_off (by omega),
    G.sb_toNat (by omega)]
  omega

theorem Geo.pa_keep (G : Geo m0 bp B) {p t : Nat} (hp : p < 256) (ht : t < 40) (ls : Nat) :
    Keep m0 ls p (pa m0 p + BitVec.ofNat 64 t) := by
  have := G.nxNw
  refine .inr (.inr (.inr ?_))
  unfold nodesBytes
  rw [Sym.inRange_iff (by rw [toNat_off (by omega)]; omega), toNat_off (by omega),
    G.pa_toNat (by omega)]
  omega

theorem Geo.sb_outs (G : Geo m0 bp B) {i t : Nat} (hi : i < 256) (ht : t < 40) :
    outs (rdr m0) (W m0) (sb m0 i + BitVec.ofNat 64 t) := by
  have := G.sbNw
  refine .inr (.inl ?_)
  unfold nodesBytes
  rw [Sym.inRange_iff (by omega), G.sb_toNat (by omega)]
  omega

theorem Geo.pa_outs (G : Geo m0 bp B) {p t : Nat} (hp : p < 256) (ht : t < 40) :
    outs (rdr m0) (W m0) (pa m0 p + BitVec.ofNat 64 t) := by
  have := G.nxNw
  refine .inr (.inr ?_)
  unfold nodesBytes
  rw [Sym.inRange_iff (by omega), G.pa_toNat (by omega)]
  omega

/-- **The frame after a block** writing the frame (not its slots) and region `r1` of outputs. -/
theorem Geo.frm_block (G : Geo m0 bp B) {m m' : MachineData} {env : Env} {S S' : SState}
    (hfr : Frm m0 m) (hm : Match env S m) (hm' : Match env S' m') (hwf : env.WF)
    (hd : m.dmem = env.mem0) (hsp : S'.sp = S.sp)
    (h0 : env.regions[0]? = some (base m0 224, 224)) {r1 : Nat} {b1 : BitVec 64} {sz1 : Nat}
    (hr1 : r1 ≠ 0) (hb1 : env.regions[r1]? = some (b1, sz1))
    (hout : ∀ t < sz1, outs (rdr m0) (W m0) (b1 + BitVec.ofNat 64 t))
    (hW : ∀ w ∈ S'.mem, (w.r = 0 ∧ w.off + w.n ≤ 224 ∧
      ∀ p ∈ slots, w.off + w.n ≤ p.1 ∨ p.1 + 8 ≤ w.off) ∨ (w.r = r1 ∧ w.off + w.n ≤ sz1)) :
    Frm m0 m' :=
  Fr.ofBlockW hfr hm hm' hwf hd hsp (fun x hx ↦ absurd hx (by simp)) h0 (by decide) G.g.st.2.1
    (by decide) fun w hw ↦ by
      rcases hW w hw with h | ⟨hr, hle⟩
      · exact .inl h
      · refine .inr ⟨by rw [hr]; exact hr1, fun b sz hb ↦ ?_⟩
        rw [hr, hb1] at hb
        cases hb
        exact ⟨hle, hout⟩

/-- A byte of the stack is changeable, and not the reader's cursor. -/
theorem Geo.stk (G : Geo m0 bp B) {q : BitVec 64}
    (h : InRange (base m0 climbLevelStack) climbLevelStack q) (ls lp : Nat) :
    Keep m0 ls lp q ∧ ¬InRange (rdr m0 + BitVec.ofNat 64 16) 8 q := by
  refine ⟨.inl h, fun hc ↦ ?_⟩
  have hsp := G.sp
  have := G.rNw
  have hsr : _ ∨ _ := G.g.sr
  rw [G.bN] at hsr
  rw [Sym.inRange_iff (by rw [G.bN]; omega), G.bN] at h
  rw [Sym.inRange_iff (by rw [toNat_off (by omega)]; omega), toNat_off (by omega)] at hc
  omega

/-- A byte of the frame is a byte of the stack. -/
theorem Geo.frame_stk (G : Geo m0 bp B) {o : Nat} (ho : o < 224) :
    InRange (base m0 climbLevelStack) climbLevelStack (base m0 224 + BitVec.ofNat 64 o) := by
  have hsp := G.sp
  rw [Sym.inRange_iff (by rw [G.bN]; omega), G.bN, toNat_off (by rw [G.bF]; omega), G.bF]
  unfold climbLevelStack at hsp ⊢
  omega

theorem Geo.sb_cur (G : Geo m0 bp B) {i t : Nat} (hi : i < 256) (ht : t < 40) :
    ¬InRange (rdr m0 + BitVec.ofNat 64 16) 8 (sb m0 i + BitVec.ofNat 64 t) := fun hc ↦ by
  have := G.rNw; have := G.sbNw; have := G.sR
  rw [Sym.inRange_iff (by rw [toNat_off (by omega)]; omega), toNat_off (by omega),
    G.sb_toNat (by omega)] at hc
  omega

theorem Geo.pa_cur (G : Geo m0 bp B) {p t : Nat} (hp : p < 256) (ht : t < 40) :
    ¬InRange (rdr m0 + BitVec.ofNat 64 16) 8 (pa m0 p + BitVec.ofNat 64 t) := fun hc ↦ by
  have := G.rNw; have := G.nxNw; have := G.xR
  rw [Sym.inRange_iff (by rw [toNat_off (by omega)]; omega), toNat_off (by omega),
    G.pa_toNat (by omega)] at hc
  omega

/-- **What a block writing the frame and region `r1` changes** is in `Keep`, not the cursor. -/
theorem Geo.written_keep (G : Geo m0 bp B) {env : Env} {S' : SState} (hwf : env.WF)
    (h0 : env.regions[0]? = some (base m0 224, 224)) {r1 : Nat} {b1 : BitVec 64} {sz1 : Nat}
    (hb1 : env.regions[r1]? = some (b1, sz1)) {ls lp : Nat}
    (hk : ∀ t < sz1, Keep m0 ls lp (b1 + BitVec.ofNat 64 t) ∧
      ¬InRange (rdr m0 + BitVec.ofNat 64 16) 8 (b1 + BitVec.ofNat 64 t))
    (hW : ∀ w ∈ S'.mem, (w.r = 0 ∧ w.off + w.n ≤ 224) ∨ (w.r = r1 ∧ w.off + w.n ≤ sz1)) :
    ∀ a, Written env S' a → Keep m0 ls lp a ∧ ¬InRange (rdr m0 + BitVec.ofNat 64 16) 8 a := by
  rintro a ⟨w, hw, b, sz, hb, h1, h2⟩
  have hnw := hwf.noWrap _ _ _ hb
  have ha : a = b + BitVec.ofNat 64 (a.toNat - b.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_off (by omega)]
    omega
  rcases hW w hw with ⟨hr, hle⟩ | ⟨hr, hle⟩
  · rw [hr, h0] at hb
    cases hb
    rw [ha]
    exact G.stk (G.frame_stk (by omega)) ls lp
  · rw [hr, hb1] at hb
    cases hb
    rw [ha]
    exact hk _ (by omega)

/-- **What a block writing the frame and region `r1` changes**, as `SameOutside`. -/
theorem Geo.block_same (G : Geo m0 bp B) {env : Env} {S' : SState} {m' : MachineData}
    (hm' : Match env S' m') (hwf : env.WF)
    (h0 : env.regions[0]? = some (base m0 224, 224)) {r1 : Nat} {b1 : BitVec 64} {sz1 : Nat}
    (hb1 : env.regions[r1]? = some (b1, sz1)) {ls lp : Nat}
    (hk : ∀ t < sz1, Keep m0 ls lp (b1 + BitVec.ofNat 64 t) ∧
      ¬InRange (rdr m0 + BitVec.ofNat 64 16) 8 (b1 + BitVec.ofNat 64 t))
    (hW : ∀ w ∈ S'.mem, (w.r = 0 ∧ w.off + w.n ≤ 224) ∨ (w.r = r1 ∧ w.off + w.n ≤ sz1)) :
    SameOutside env.mem0 m'.dmem fun a ↦ Keep m0 ls lp a ∧
      ¬InRange (rdr m0 + BitVec.ofNat 64 16) 8 a :=
  NativeRustcVm.SameOutside.mono (hm'.sameOutside hwf) (G.written_keep hwf h0 hb1 hk hW)

theorem Geo.nd0 (G : Geo m0 bp B) {j : Nat} (h : j < cnt m0) :
    (nd m0 j).toNat = (nodes m0).toNat + 40 * j := by
  have := G.ndNw; rw [toNat_off (by omega)]

theorem Geo.sb0 (G : Geo m0 bp B) {i : Nat} (h : i < 256) :
    (sb m0 i).toNat = (sibs m0).toNat + 40 * i := by
  have := G.sbNw; rw [toNat_off (by omega)]

theorem Geo.ndMap' (G : Geo m0 bp B) {j n : Nat} (h : j < cnt m0) (hn : n ≤ 40) :
    NativeRustcVm.Mapped m0.dmem (nd m0 j) n := fun t ht ↦ by
  rw [NativeRustcVm.addr_add_add]; exact G.ndMap _ (by omega)

theorem Geo.sbMap' (G : Geo m0 bp B) {i : Nat} (h : i < 256) :
    NativeRustcVm.Mapped m0.dmem (sb m0 i) 40 := fun t ht ↦ by
  rw [NativeRustcVm.addr_add_add]; exact G.sbMap _ (by unfold nodesBytes; omega)

omit [Labels] in
theorem stack224 : 224 ≤ climbLevelStack := by decide

/-- **A node written** by a block: its key's and its digest's words, each a write of a value. -/
theorem node_write {env : Env} {S : SState} {m : MachineData} (hm : Match env S m) {r : Nat}
    {b : BitVec 64} (hb : env.regions[r]? = some (b, 40)) {v0 v1 v2 v3 v4 : Sym}
    (hw0 : ∀ i < 8, findWrite r (0 + i) S.mem = some (v0, i))
    (hw1 : ∀ i < 8, findWrite r (8 + i) S.mem = some (v1, i))
    (hw2 : ∀ i < 8, findWrite r (16 + i) S.mem = some (v2, i))
    (hw3 : ∀ i < 8, findWrite r (24 + i) S.mem = some (v3, i))
    (hw4 : ∀ i < 8, findWrite r (32 + i) S.mem = some (v4, i)) {x : Nat × Digest}
    (hk : x.1 < 2 ^ 64) (e0 : UInt64.ofBitVec (v0.eval env) = x.1.toUInt64)
    (e1 : UInt64.ofBitVec (v1.eval env) = x.2[0]) (e2 : UInt64.ofBitVec (v2.eval env) = x.2[1])
    (e3 : UInt64.ofBitVec (v3.eval env) = x.2[2]) (e4 : UInt64.ofBitVec (v4.eval env) = x.2[3]) :
    NodeAt m.dmem b x := by
  have w : ∀ {o : Nat} {v : Sym} {u : UInt64}, o + 8 ≤ 40 →
      (∀ i < 8, findWrite r (o + i) S.mem = some (v, i)) → UInt64.ofBitVec (v.eval env) = u →
      WordAt m.dmem (b + BitVec.ofNat 64 o) u := fun ho hw he ↦ by
    have h := hm.bytesAt_write hb ho hw
    rw [byteOf_range, he] at h
    exact h
  have h0 := w (o := 0) (by omega) hw0 e0
  rw [NativeRustcVm.addr_add_zero] at h0
  exact nodeAt_iff.mpr ⟨hk, h0, w (by omega) hw1 e1, w (by omega) hw2 e2, w (by omega) hw3 e3,
    w (by omega) hw4 e4⟩

omit [Labels] in
/-- A word the environment loads in region `r`, from the word at its address. -/
theorem load_of {env : Env} {r o : Nat} {b : BitVec 64} {n : Nat}
    (hb : env.regions[r]? = some (b, n)) {u : UInt64}
    (h : WordAt env.mem0 (b + BitVec.ofNat 64 o) u) : env.load r o 8 = u.toBitVec :=
  load_word (by rw [Env.base_eq hb]; exact h)

omit [Labels] in
/-- The registers the set-up fixed, kept. -/
theorem Fix.keep {m m' : MachineData} (h : Fix m0 m)
    (he : ∀ r ∈ [XReg.X22, .X25, .X27, .X28, .X29], m'.regs.getXReg r = m.regs.getXReg r) :
    Fix m0 m' :=
  ⟨by rw [he .X22 (by simp)]; exact h.x22, by rw [he .X25 (by simp)]; exact h.x25,
    by rw [he .X27 (by simp)]; exact h.x27, by rw [he .X28 (by simp)]; exact h.x28,
    by rw [he .X29 (by simp)]; exact h.x29⟩

omit [Labels] in
/-- The reader's address, at SP+8. -/
theorem load_rdr {m : MachineData} (hfr : Frm m0 m) {rs : List (BitVec 64 × Nat)} :
    (Env.ofMachine m ((base m0 224, 224) :: rs)).load 0 8 8 = rdr m0 :=
  load_word (hfr.slots (8, .X0) (by simp [slots]))

omit [Labels] in
/-- The parents' address, at SP+16. -/
theorem load_nxt {m : MachineData} (hfr : Frm m0 m) {rs : List (BitVec 64 × Nat)} :
    (Env.ofMachine m ((base m0 224, 224) :: rs)).load 0 16 8 = nxt m0 :=
  load_word (hfr.slots (16, .X4) (by simp [slots]))

end

end NativeRustcVmArm.Wire.ClimbLevel
