module

public import NativeRustcVmArm.Wire.ClimbLevel.Exec
public import NativeRustcVmArm.Wire.Frame
public import NativeRustcVmArm.Wire.Common
public import NativeRustcVmArm.Spec.Wire
public import NativeRustcVm.Wire.ClimbFacts
public import NativeRustcVmArm.Transcript.Stack

/-!
# `climb_level`'s places

The nodes at X1 (`nd i`), the siblings at X3 (`sb i`) and the parents at X4 (`pa p`), 40 bytes
each; the outputs `W` (the siblings' and the parents' arrays); the frame (`Frm`, 224 bytes: the
callee-saved registers, the reader at SP+8 and the parents' address at SP+16). `Geo`: where
everything is, as numbers. `Keep ls lp`: what a step may change, the stack, the reader's cursor,
the siblings from `ls` and the parents from `lp`; what survives it (`nodesAt_keep`,
`Geo.keep_reader`).
-/

namespace NativeRustcVmArm.Wire.ClimbLevel

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.ClimbLevel
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- The prologue's slots: the reader and the parents' address, the callee-saved registers. -/
def slots : List (Nat × XReg) := [(8, .X0), (16, .X4), (128, .X29), (136, .X30), (144, .X28),
  (152, .X27), (160, .X26), (168, .X25), (176, .X24), (184, .X23), (192, .X22), (200, .X21),
  (208, .X20), (216, .X19)]

/-- The reader's address. -/
abbrev rdr (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
/-- The nodes' address. -/
abbrev nodes (m0 : MachineData) : BitVec 64 := m0.regs.X1.toBitVec
/-- The nodes' count. -/
abbrev cnt (m0 : MachineData) : Nat := m0.regs.X2.toNat
/-- The siblings' address. -/
abbrev sibs (m0 : MachineData) : BitVec 64 := m0.regs.X3.toBitVec
/-- The parents' address. -/
abbrev nxt (m0 : MachineData) : BitVec 64 := m0.regs.X4.toBitVec
/-- Node `i`'s address. -/
abbrev nd (m0 : MachineData) (i : Nat) : BitVec 64 := nodes m0 + BitVec.ofNat 64 (40 * i)
/-- Sibling `i`'s address. -/
abbrev sb (m0 : MachineData) (i : Nat) : BitVec 64 := sibs m0 + BitVec.ofNat 64 (40 * i)
/-- Parent `p`'s address. -/
abbrev pa (m0 : MachineData) (p : Nat) : BitVec 64 := nxt m0 + BitVec.ofNat 64 (40 * p)
/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := base m0 224

/-- The outputs: the siblings' and the parents' arrays. -/
abbrev W (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange (sibs m0) nodesBytes q ∨ InRange (nxt m0) nodesBytes q

/-- The state between the prologue and the epilogue. -/
abbrev Frm (m0 m : MachineData) : Prop :=
  Fr m0 224 climbLevelStack slots [] (outs (rdr m0) (W m0)) m

/-- What `climb_level` reaches. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ ClimbLevelPost m0 st.data

/-- The environment of the frame. -/
abbrev frEnv (m0 m : MachineData) : Env := Env.ofMachine m [(base m0 224, 224)]

/-- What a step may change: the stack, the reader's cursor, the siblings from `ls`, the parents
from `lp`. -/
def Keep (m0 : MachineData) (ls lp : Nat) (q : BitVec 64) : Prop :=
  InRange (base m0 climbLevelStack) climbLevelStack q ∨
    InRange (rdr m0 + BitVec.ofNat 64 16) 8 q ∨
    InRange (sb m0 ls) (nodesBytes - 40 * ls) q ∨ InRange (pa m0 lp) (nodesBytes - 40 * lp) q

/-- **The places**, as numbers: the stack below SP, the reader and its bytes, the nodes, the
siblings, the parents and the round constants, pairwise apart. -/
structure Geo [Labels] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) : Prop where
  g : RGeo m0 climbLevelStack (rdr m0) bp B.length (W m0)
  rc : RcAt m0 climbLevelStack
  n256 : cnt m0 ≤ 256
  ndMap : NativeRustcVm.Mapped m0.dmem (nodes m0) (40 * cnt m0)
  sbMap : NativeRustcVm.Mapped m0.dmem (sibs m0) nodesBytes
  nxMap : NativeRustcVm.Mapped m0.dmem (nxt m0) nodesBytes
  ndNw : (nodes m0).toNat + 40 * cnt m0 ≤ 2 ^ 64
  sbNw : (sibs m0).toNat + 10240 ≤ 2 ^ 64
  nxNw : (nxt m0).toNat + 10240 ≤ 2 ^ 64
  nS : (nodes m0).toNat + 40 * cnt m0 ≤ m0.regs.SP.toNat - climbLevelStack ∨
    m0.regs.SP.toNat ≤ (nodes m0).toNat
  sS : (sibs m0).toNat + 10240 ≤ m0.regs.SP.toNat - climbLevelStack ∨
    m0.regs.SP.toNat ≤ (sibs m0).toNat
  xS : (nxt m0).toNat + 10240 ≤ m0.regs.SP.toNat - climbLevelStack ∨
    m0.regs.SP.toNat ≤ (nxt m0).toNat
  nR : (nodes m0).toNat + 40 * cnt m0 ≤ (rdr m0).toNat ∨ (rdr m0).toNat + 24 ≤ (nodes m0).toNat
  sR : (sibs m0).toNat + 10240 ≤ (rdr m0).toNat ∨ (rdr m0).toNat + 24 ≤ (sibs m0).toNat
  xR : (nxt m0).toNat + 10240 ≤ (rdr m0).toNat ∨ (rdr m0).toNat + 24 ≤ (nxt m0).toNat
  nB : (nodes m0).toNat + 40 * cnt m0 ≤ bp.toNat ∨ bp.toNat + B.length ≤ (nodes m0).toNat
  nSb : (nodes m0).toNat + 40 * cnt m0 ≤ (sibs m0).toNat ∨ (sibs m0).toNat + 10240 ≤ (nodes m0).toNat
  nX : (nodes m0).toNat + 40 * cnt m0 ≤ (nxt m0).toNat ∨ (nxt m0).toNat + 10240 ≤ (nodes m0).toNat
  sX : (sibs m0).toNat + 10240 ≤ (nxt m0).toNat ∨ (nxt m0).toNat + 10240 ≤ (sibs m0).toNat
  rR : rcAddr.toNat + 192 ≤ (rdr m0).toNat ∨ (rdr m0).toNat + 24 ≤ rcAddr.toNat
  rS : rcAddr.toNat + 192 ≤ (sibs m0).toNat ∨ (sibs m0).toNat + 10240 ≤ rcAddr.toNat
  rX : rcAddr.toNat + 192 ≤ (nxt m0).toNat ∨ (nxt m0).toNat + 10240 ≤ rcAddr.toNat

end

public section

theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit} (h : exec ds S = some (S₁, x)) :
    after ds S = S₁ := by
  rw [after, h]

theorem toNat_off {a : BitVec 64} {o : Nat} (h : a.toNat + o < 2 ^ 64) :
    (a + BitVec.ofNat 64 o).toNat = a.toNat + o :=
  NativeRustcVm.toNat_add_ofNat h

/-- **Nodes survive** a change of memory away from them. -/
theorem nodesAt_keep {d d' : Mem 64} {a : BitVec 64} {l : List (Nat × Digest)}
    {R : BitVec 64 → Prop} (h : NodesAt d a l) (hs : SameOutside d d' R)
    (hnw : a.toNat + 40 * l.length ≤ 2 ^ 64)
    (hR : ∀ q, R q → q.toNat < a.toNat ∨ a.toNat + 40 * l.length ≤ q.toNat) : NodesAt d' a l :=
  h.of_sameOutside hs fun i hi hq ↦ by
    have := hR _ hq
    rw [toNat_off (by omega)] at this
    omega

/-- **Words survive** a change of memory away from them. -/
theorem wordsAt_keep {d d' : Mem 64} {a : BitVec 64} {ws : List UInt64}
    {R : BitVec 64 → Prop} (h : WordsAt d a ws) (hs : SameOutside d d' R)
    (hnw : a.toNat + 8 * ws.length ≤ 2 ^ 64)
    (hR : ∀ q, R q → q.toNat < a.toNat ∨ a.toNat + 8 * ws.length ≤ q.toNat) : WordsAt d' a ws :=
  NativeRustcVm.BytesAt.of_sameOutside h hs fun i hi hq ↦ by
    rw [NativeRustcVm.length_wordsBytes] at hi
    have := hR _ hq
    rw [toNat_off (by omega)] at this
    omega

theorem wordAt_keep {d d' : Mem 64} {a : BitVec 64} {w : UInt64}
    {R : BitVec 64 → Prop} (h : WordAt d a w) (hs : SameOutside d d' R)
    (hnw : a.toNat + 8 ≤ 2 ^ 64)
    (hR : ∀ q, R q → q.toNat < a.toNat ∨ a.toNat + 8 ≤ q.toNat) : WordAt d' a w :=
  NativeRustcVm.BytesAt.of_sameOutside h hs fun i hi hq ↦ by
    rw [NativeRustcVm.length_wordBytes] at hi
    have := hR _ hq
    rw [toNat_off (by omega)] at this
    omega

/-- One node more, after them. -/
theorem NodesAt.append_one {d : Mem 64} {a : BitVec 64} {l : List (Nat × Digest)}
    {x : Nat × Digest} (h : NodesAt d a l) (hx : NodeAt d (a + BitVec.ofNat 64 (40 * l.length)) x) :
    NodesAt d a (l ++ [x]) := by
  intro j hj
  simp only [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
  · rw [List.getElem_append_left hj]; exact h j hj
  · rw [List.getElem_append_right (le_refl _)]; simpa using hx

/-- **A digest's words**, one by one. -/
theorem wordsAt_digest_iff {d : Mem 64} {a : BitVec 64} {dg : Digest} :
    WordsAt d a dg.toList ↔ WordAt d a dg[0] ∧ WordAt d (a + BitVec.ofNat 64 8) dg[1] ∧
      WordAt d (a + BitVec.ofNat 64 16) dg[2] ∧ WordAt d (a + BitVec.ofNat 64 24) dg[3] := by
  obtain ⟨⟨l⟩, hl⟩ := dg
  match l, hl with
  | [w0, w1, w2, w3], _ =>
    show WordsAt d a [w0, w1, w2, w3] ↔ _
    simp only [NativeRustcVm.wordsAt_cons_iff, NativeRustcVm.addr_add_add]
    rw [show WordsAt d (a + BitVec.ofNat 64 (8 + 8 + 8 + 8)) [] ↔ True from
      iff_true_intro (NativeRustcVm.wordsAt_nil _ _), and_true]
    rfl

/-- **A node's words**: its key, its digest's. -/
theorem nodeAt_iff {d : Mem 64} {a : BitVec 64} {x : Nat × Digest} :
    NodeAt d a x ↔ x.1 < 2 ^ 64 ∧ WordAt d a x.1.toUInt64 ∧ WordAt d (a + BitVec.ofNat 64 8) x.2[0] ∧
      WordAt d (a + BitVec.ofNat 64 16) x.2[1] ∧ WordAt d (a + BitVec.ofNat 64 24) x.2[2] ∧
      WordAt d (a + BitVec.ofNat 64 32) x.2[3] := by
  unfold NodeAt
  rw [show NativeRustcVm.Transcript.off a 8 = a + BitVec.ofNat 64 8 from rfl, wordsAt_digest_iff]
  simp only [NativeRustcVm.addr_add_add]

/-- The digest of four words. -/
theorem digest_eta (dg : Digest) : (#v[dg[0], dg[1], dg[2], dg[3]] : Digest) = dg := by
  obtain ⟨⟨l⟩, hl⟩ := dg
  match l, hl with
  | [_, _, _, _], _ => rfl

theorem xor_toNat (a b : UInt64) : (a.toBitVec ^^^ b.toBitVec).toNat = a.toNat ^^^ b.toNat := by
  rw [BitVec.toNat_xor]; rfl

/-- `lsr x, #1` (`ubfm x, #1, #63`). -/
theorem lsr1 (x : BitVec 64) : (UnOp.apply (.ubfm 1 63) .W64 x).toNat = x.toNat / 2 := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64]
  simp [evalUBFM, toNat_take', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

section Geo
variable [Labels] {m0 : MachineData} {bp : BitVec 64} {B : List UInt8}

theorem Geo.sp (G : Geo m0 bp B) : m0.regs.SP.toNat % 16 = 0 ∧ climbLevelStack ≤ m0.regs.SP.toNat ∧
    m0.regs.SP.toNat < 2 ^ 64 := ⟨G.g.st.1, G.g.st.2.1, m0.regs.SP.toNat_lt⟩

theorem Geo.bN (G : Geo m0 bp B) :
    (base m0 climbLevelStack).toNat = m0.regs.SP.toNat - climbLevelStack :=
  Ring.base_toNat G.g.st.2.1

theorem Geo.bF (G : Geo m0 bp B) : (base m0 224).toNat = m0.regs.SP.toNat - 224 :=
  Ring.base_toNat (by have := G.g.st.2.1; unfold climbLevelStack at this; omega)

theorem Geo.rNw (G : Geo m0 bp B) : (rdr m0).toNat + 24 ≤ 2 ^ 64 := G.g.rNw

omit [Labels] in
/-- A byte of the tail of an array of 256 nodes from node `l`, as a number. -/
theorem inRange_tail {a q : BitVec 64} (hnw : a.toNat + 10240 ≤ 2 ^ 64) {l : Nat} (hl : l ≤ 256)
    (h : InRange (a + BitVec.ofNat 64 (40 * l)) (nodesBytes - 40 * l) q) :
    a.toNat + 40 * l ≤ q.toNat ∧ q.toNat < a.toNat + 10240 := by
  unfold nodesBytes at h
  rcases Nat.lt_or_ge l 256 with hl' | hl'
  · rw [Sym.inRange_iff (by rw [toNat_off (by omega)]; omega), toNat_off (by omega)] at h
    omega
  · unfold InRange at h; omega

/-- **What a step may change**, as numbers. -/
theorem Geo.keep_toNat (G : Geo m0 bp B) {ls lp : Nat} (hls : ls ≤ 256) (hlp : lp ≤ 256)
    {q : BitVec 64} (h : Keep m0 ls lp q) :
    (m0.regs.SP.toNat - climbLevelStack ≤ q.toNat ∧ q.toNat < m0.regs.SP.toNat) ∨
      ((rdr m0).toNat + 16 ≤ q.toNat ∧ q.toNat < (rdr m0).toNat + 24) ∨
      ((sibs m0).toNat + 40 * ls ≤ q.toNat ∧ q.toNat < (sibs m0).toNat + 10240) ∨
      ((nxt m0).toNat + 40 * lp ≤ q.toNat ∧ q.toNat < (nxt m0).toNat + 10240) := by
  have hsp := G.sp
  have := G.rNw
  have := G.sbNw
  have := G.nxNw
  unfold Keep nodesBytes at h
  rcases h with h | h | h | h
  · rw [Sym.inRange_iff (by rw [G.bN]; omega), G.bN] at h
    omega
  · rw [Sym.inRange_iff (by rw [toNat_off (by omega)]; omega), toNat_off (by omega)] at h
    omega
  · exact .inr (.inr (.inl (inRange_tail (by omega) hls h)))
  · exact .inr (.inr (.inr (inRange_tail (by omega) hlp h)))

/-- The nodes survive a step. -/
theorem Geo.keep_nodes (G : Geo m0 bp B) {ls lp : Nat} (hls : ls ≤ 256) (hlp : lp ≤ 256)
    {d d' : Mem 64} (hs : SameOutside d d' (Keep m0 ls lp)) {l : List (Nat × Digest)}
    (hl : l.length = cnt m0) (h : NodesAt d (nodes m0) l) : NodesAt d' (nodes m0) l :=
  nodesAt_keep h hs (by rw [hl]; exact G.ndNw) fun q hq ↦ by
    have := G.keep_toNat hls hlp hq
    have := G.nS; have := G.nR; have := G.nSb; have := G.nX
    rw [hl]
    omega

/-- The siblings before `ls` survive a step. -/
theorem Geo.keep_sibs (G : Geo m0 bp B) {ls lp : Nat} (hls : ls ≤ 256) (hlp : lp ≤ 256)
    {d d' : Mem 64} (hs : SameOutside d d' (Keep m0 ls lp)) {l : List (Nat × Digest)}
    (hl : l.length ≤ ls) (h : NodesAt d (sibs m0) l) : NodesAt d' (sibs m0) l :=
  nodesAt_keep h hs (by have := G.sbNw; omega) fun q hq ↦ by
    have := G.keep_toNat hls hlp hq
    have := G.sS; have := G.sR; have := G.sX
    omega

/-- The parents before `lp` survive a step. -/
theorem Geo.keep_nxt (G : Geo m0 bp B) {ls lp : Nat} (hls : ls ≤ 256) (hlp : lp ≤ 256)
    {d d' : Mem 64} (hs : SameOutside d d' (Keep m0 ls lp)) {l : List (Nat × Digest)}
    (hl : l.length ≤ lp) (h : NodesAt d (nxt m0) l) : NodesAt d' (nxt m0) l :=
  nodesAt_keep h hs (by have := G.nxNw; omega) fun q hq ↦ by
    have := G.keep_toNat hls hlp hq
    have := G.xS; have := G.xR; have := G.sX
    omega

/-- The reader survives a step that does not move its cursor. -/
theorem Geo.keep_reader (G : Geo m0 bp B) {ls lp : Nat} (hls : ls ≤ 256) (hlp : lp ≤ 256)
    {d d' : Mem 64} {R : BitVec 64 → Prop} (hs : SameOutside d d' R)
    (hR : ∀ q, R q → Keep m0 ls lp q ∧ ¬InRange (rdr m0 + BitVec.ofNat 64 16) 8 q) {c : Nat}
    (h : ReaderAt d (rdr m0) bp B c) : ReaderAt d' (rdr m0) bp B c := by
  refine G.g.reader_frame rfl h (NativeRustcVm.SameOutside.mono hs fun q hq ↦ ?_)
  obtain ⟨hk, hc⟩ := hR q hq
  unfold Keep at hk
  rcases hk with hk | hk | hk | hk
  · exact .inl hk
  · exact absurd hk hc
  · refine .inr (.inl ?_)
    have := G.sbNw
    have := inRange_tail (by omega) hls hk
    rw [Sym.inRange_iff (by unfold nodesBytes; omega)]
    unfold nodesBytes
    omega
  · refine .inr (.inr ?_)
    have := G.nxNw
    have := inRange_tail (by omega) hlp hk
    rw [Sym.inRange_iff (by unfold nodesBytes; omega)]
    unfold nodesBytes
    omega

/-- A byte of the frame is a byte of the stack, hence kept-changeable. -/
theorem Geo.frame_keep (G : Geo m0 bp B) {o : Nat} (ho : o < 224) (ls lp : Nat) :
    Keep m0 ls lp (base m0 224 + BitVec.ofNat 64 o) := by
  have hsp := G.sp
  refine .inl ?_
  rw [Sym.inRange_iff (by rw [G.bN]; omega), G.bN, toNat_off (by rw [G.bF]; omega), G.bF]
  unfold climbLevelStack at hsp ⊢
  omega

/-- The bytes of `Fr`'s change (the stack, the cursor, the outputs) miss the nodes. -/
theorem Geo.nodes_frm (G : Geo m0 bp B) {ns : List (Nat × Digest)} (hl : ns.length = cnt m0)
    (h : NodesAt m0.dmem (nodes m0) ns) {m : MachineData} (hfr : Frm m0 m) :
    NodesAt m.dmem (nodes m0) ns :=
  nodesAt_keep h hfr.same (by rw [hl]; exact G.ndNw) fun q hq ↦ by
    have hsp := G.sp
    have := G.rNw; have := G.sbNw; have := G.nxNw
    have := G.nS; have := G.nR; have := G.nSb; have := G.nX
    rw [hl]
    rcases hq with hq | hq | hq | hq
    · rw [Sym.inRange_iff (by rw [G.bN]; omega), G.bN] at hq; omega
    · rw [Sym.inRange_iff (by rw [toNat_off (by omega)]; omega), toNat_off (by omega)] at hq
      omega
    · rw [Sym.inRange_iff (by unfold nodesBytes; omega)] at hq; unfold nodesBytes at hq; omega
    · rw [Sym.inRange_iff (by unfold nodesBytes; omega)] at hq; unfold nodesBytes at hq; omega

/-- The round constants for a callee using `n'` bytes of stack below the frame. -/
theorem Geo.rc_frm (G : Geo m0 bp B) {m : MachineData} (hfr : Frm m0 m) {n' : Nat}
    (hn' : n' ≤ climbLevelStack - 224) : RcAt m n' := by
  have hsp := G.sp
  have hrc := G.rc
  have hnw : rcAddr.toNat + 192 ≤ 2 ^ 64 := hrc.2.1
  have hap : rcAddr.toNat + 192 ≤ (stackBelow m0 climbLevelStack).toNat ∨
      (stackBelow m0 climbLevelStack).toNat + climbLevelStack ≤ rcAddr.toNat := hrc.2.2
  refine Transcript.RcAt.callee (F := 224) hrc (Transcript.rc_keep hfr.same fun q hq hin ↦ ?_)
    G.g.st.2.1
    (by unfold climbLevelStack; omega) ?_ hn'
  · have := G.rNw; have := G.sbNw; have := G.nxNw
    have := G.rR; have := G.rS; have := G.rX
    rw [NativeRustcVm.inRange_iff (show NativeRustcVm.NoWrap rcAddr 192 from hnw)] at hin
    rw [show (stackBelow m0 climbLevelStack).toNat = m0.regs.SP.toNat - climbLevelStack from G.bN]
      at hap
    rcases hq with hq | hq | hq | hq
    · rw [Sym.inRange_iff (by rw [G.bN]; omega), G.bN] at hq; omega
    · rw [Sym.inRange_iff (by rw [toNat_off (by omega)]; omega), toNat_off (by omega)] at hq
      omega
    · rw [Sym.inRange_iff (by unfold nodesBytes; omega)] at hq; unfold nodesBytes at hq; omega
    · rw [Sym.inRange_iff (by unfold nodesBytes; omega)] at hq; unfold nodesBytes at hq; omega
  · show m.regs.SP.toBitVec.toNat = _
    rw [hfr.sp, G.bF]

/-- The frame's environment is well formed. -/
theorem Geo.frEnv_wf (G : Geo m0 bp B) {m : MachineData} (hfr : Frm m0 m) : (frEnv m0 m).WF :=
  Env.wf_of ⟨⟨fun j hj ↦ hfr.kept _ (Ring.frame_mapped G.g.st (by decide) j hj),
    Ring.base_noWrap (by have := G.g.st.2.1; unfold climbLevelStack at this; omega)⟩, trivial⟩
    (List.pairwise_singleton _ _)

theorem Geo.aligned (G : Geo m0 bp B) : (base m0 224).toNat % 16 = 0 :=
  Ring.frame_aligned G.g.st (by decide) (by decide)

theorem Geo.frEnv_match (G : Geo m0 bp B) {m : MachineData} (hfr : Frm m0 m) :
    Match (frEnv m0 m) frS m :=
  match_ofMachine ⟨rfl, fun _ ↦ G.aligned, trivial⟩ (by rw [hfr.sp]; simp [Sym.eval])
    trivial trivial trivial trivial

/-- The frame and two more regions: a well formed environment. -/
theorem Geo.env2_wf (G : Geo m0 bp B) {m : MachineData} (hfr : Frm m0 m) {a : BitVec 64}
    {n : Nat} (hmap : NativeRustcVm.Mapped m0.dmem a n) (hnw : a.toNat + n ≤ 2 ^ 64)
    (hap : a.toNat + n ≤ m0.regs.SP.toNat - 224 ∨ m0.regs.SP.toNat ≤ a.toNat) :
    (Env.ofMachine m [(base m0 224, 224), (a, n)]).WF := by
  have hsp := G.sp
  refine Env.wf_of ⟨⟨fun j hj ↦ hfr.kept _ (Ring.frame_mapped G.g.st (by decide) j hj),
    Ring.base_noWrap (by unfold climbLevelStack at hsp; omega)⟩,
    ⟨fun j hj ↦ hfr.kept _ (hmap j hj), hnw⟩, trivial⟩ (List.pairwise_pair.mpr ?_)
  show (base m0 224).toNat + 224 ≤ a.toNat ∨ a.toNat + n ≤ (base m0 224).toNat
  rw [G.bF]
  unfold climbLevelStack at hsp
  omega

/-- The frame and three more regions: a well formed environment. -/
theorem Geo.env3_wf (G : Geo m0 bp B) {m : MachineData} (hfr : Frm m0 m) {a b : BitVec 64}
    {n k : Nat} (hmap : NativeRustcVm.Mapped m0.dmem a n) (hnw : a.toNat + n ≤ 2 ^ 64)
    (hap : a.toNat + n ≤ m0.regs.SP.toNat - 224 ∨ m0.regs.SP.toNat ≤ a.toNat)
    (hmap' : NativeRustcVm.Mapped m0.dmem b k) (hnw' : b.toNat + k ≤ 2 ^ 64)
    (hap' : b.toNat + k ≤ m0.regs.SP.toNat - 224 ∨ m0.regs.SP.toNat ≤ b.toNat)
    (hab : a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat) :
    (Env.ofMachine m [(base m0 224, 224), (a, n), (b, k)]).WF := by
  have hsp := G.sp
  refine Env.wf_of ⟨⟨fun j hj ↦ hfr.kept _ (Ring.frame_mapped G.g.st (by decide) j hj),
    Ring.base_noWrap (by unfold climbLevelStack at hsp; omega)⟩,
    ⟨fun j hj ↦ hfr.kept _ (hmap j hj), hnw⟩, ⟨fun j hj ↦ hfr.kept _ (hmap' j hj), hnw'⟩, trivial⟩
    (List.pairwise_cons.mpr ⟨fun e he ↦ ?_, List.pairwise_pair.mpr hab⟩)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  unfold climbLevelStack at hsp
  rcases he with rfl | rfl
  · show (base m0 224).toNat + 224 ≤ a.toNat ∨ a.toNat + n ≤ (base m0 224).toNat
    rw [G.bF]; omega
  · show (base m0 224).toNat + 224 ≤ b.toNat ∨ b.toNat + k ≤ (base m0 224).toNat
    rw [G.bF]; omega

/-- Node `i` (from byte `o`) as a number. -/
theorem Geo.nd_toNat (G : Geo m0 bp B) {i o : Nat} (h : 40 * i + o < 40 * cnt m0) :
    (nd m0 i + BitVec.ofNat 64 o).toNat = (nodes m0).toNat + 40 * i + o := by
  have := G.ndNw
  rw [NativeRustcVm.addr_add_add, toNat_off (by omega)]
  omega

theorem Geo.sb_toNat (G : Geo m0 bp B) {i o : Nat} (h : 40 * i + o < 10240) :
    (sb m0 i + BitVec.ofNat 64 o).toNat = (sibs m0).toNat + 40 * i + o := by
  have := G.sbNw
  rw [NativeRustcVm.addr_add_add, toNat_off (by omega)]
  omega

theorem Geo.pa_toNat (G : Geo m0 bp B) {i o : Nat} (h : 40 * i + o < 10240) :
    (pa m0 i + BitVec.ofNat 64 o).toNat = (nxt m0).toNat + 40 * i + o := by
  have := G.nxNw
  rw [NativeRustcVm.addr_add_add, toNat_off (by omega)]
  omega

end Geo

end

end NativeRustcVmArm.Wire.ClimbLevel
