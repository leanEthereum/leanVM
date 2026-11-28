module

public import NativeRustcX64.SphincsVerify.Fors.Model
public import NativeRustcX64.SphincsVerify.Fors.Exec
public import NativeRustcX64.SphincsVerify.Fors.Window
public import NativeRustcX64.SphincsVerify.Chains.StepBase

/-!
# What the FORS region keeps (x86-64)

Through tree `c` the inputs, the first layer's chain values' address (`184`), the index (`552`),
the bottom key's tree and key pair words (`80`, `68`), the 24 leaves (`10384`) and the roots so far
(`20172`) stay (`Base`); within the tree's nodes also its spills: the opening's address (`72`),
the leaf index (`88`) (`Spills`). `Keep0`/`Keep`: those and the frame's
invariant; `KeepC0`/`KeepC`: at a call. A block whose writes miss the kept bytes keeps them
(`keepOK0`, `keepOK`, decided on the literal state; `Keep0.of_block`, `Keep.of_block`, ...); a call
changing only scratch bytes (`Scratch`: `560 .. 10384`) and its stack keeps them
(`Keep0.of_call`, `Keep.of_call`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Fors

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The 24 leaves' words. -/
def leavesBytes (r : Run) : List UInt8 := Native.Keccak.wordsBytes (r.leaves.map Nat.toUInt64)

/-- The roots of the first `c` trees. -/
def rootsUpTo (r : Run) (c : Nat) : List UInt8 := ((List.range c).map r.forsRoot).flatten

/-- **What the FORS region keeps** before tree `c`. -/
structure Base (r : Run) (c : Nat) (m : MachineData) : Prop where
  hc : c < 24
  inputs : r.Inputs m
  w176 : r.WordAt m 184 (r.addr 25212)
  w568 : r.WordAt m 552 r.idx
  w80 : BytesAt m.dmem (r.off 80) (be64 (r.key 0).tree)
  w60 : BytesAt m.dmem (r.off 68) (be32 (r.key 0).leaf)
  leaves : BytesAt m.dmem (r.off 10384) (leavesBytes r)
  roots : BytesAt m.dmem (r.off 20172) (rootsUpTo r c)

/-- Tree `c`'s spills: its opening's address, its leaf index. -/
def Spills (r : Run) (c : Nat) (m : MachineData) : Prop :=
  r.WordAt m 104 (r.addr (20556 + 176 * c)) ∧ r.WordAt m 72 (r.leafOf c).toUInt64

/-- The frame and what the region keeps. -/
def Keep0 (r : Run) (c : Nat) (m : MachineData) : Prop := r.Frame m ∧ Base r c m

/-- At a call, what the region keeps. -/
def KeepC0 (r : Run) (c : Nat) (m : MachineData) : Prop := r.AtCall m ∧ Base r c m

/-- The frame, what the region keeps, the tree's spills. -/
def Keep (r : Run) (c : Nat) (m : MachineData) : Prop := r.Frame m ∧ Base r c m ∧ Spills r c m

/-- At a call, what the region keeps, the tree's spills. -/
def KeepC (r : Run) (c : Nat) (m : MachineData) : Prop :=
  r.AtCall m ∧ Base r c m ∧ Spills r c m

/-- **Bytes a step keeps**, where its literal state does not write them. -/
def KeptBy (r : Run) (S : SState) (m m' : MachineData) : Prop :=
  ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 29400 → Run.noWriteIn S o bs.length = true →
    BytesAt m.dmem (r.off o) bs → BytesAt m'.dmem (r.off o) bs

/-- The frame's scratch bytes `a .. a + n` the region's calls change. -/
abbrev Scratch (a n : Nat) : Prop := 560 ≤ a ∧ a + n ≤ 10384

/-- A block's literal state keeps `Base`: its writes in the frame below the saved registers (or
the slots below it) and off the kept bytes. -/
def keepOK0 (S : SState) : Bool :=
  Run.frameWrites S && Run.noWriteIn S 68 4 && Run.noWriteIn S 80 8 &&
    Run.noWriteIn S 112 32 && Run.noWriteIn S 184 8 && Run.noWriteIn S 552 8 &&
    Run.noWriteIn S 10384 192 && Run.noWriteIn S 20172 8124

/-- A block's literal state keeps `Base` and the tree's spills. -/
def keepOK (S : SState) : Bool :=
  keepOK0 S && Run.noWriteIn S 104 8 && Run.noWriteIn S 72 8

end

public section

theorem length_leavesBytes (r : Run) : (leavesBytes r).length = 192 := by
  rw [leavesBytes, Native.Keccak.Proof.length_wordsBytes, List.length_map, r.length_leaves]

theorem length_rootsUpTo (r : Run) {c : Nat} (hc : c ≤ 24) : (rootsUpTo r c).length = 16 * c := by
  unfold rootsUpTo
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, List.length_append, ih (by omega)]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [r.forsRoot_eq (by omega), r.length_forsUpTo]
    omega

/-- One root more. -/
theorem rootsUpTo_succ (r : Run) (c : Nat) :
    rootsUpTo r (c + 1) = rootsUpTo r c ++ r.forsRoot c := by
  simp [rootsUpTo, List.range_succ]

theorem length_be32' (v : UInt32) : (be32 v).length = 4 := rfl
theorem length_be64' (v : UInt64) : (be64 v).length = 8 := rfl

/-- Closes the frame's offset arithmetic with the lengths of the kept byte lists. -/
macro "flen" : tactic =>
  `(tactic| ((try simp only [Chains.length_pkBytes, Chains.length_sigMemR,
    NativeRustc.length_wordBytes, length_be32', length_be64', length_leavesBytes,
    List.length_replicate, List.length_map, List.length_range, List.length_append]) <;> omega))

variable [Labels] {r : Run}

omit [Labels] in
theorem Base.c_lt {c : Nat} {m : MachineData} (h : Base r c m) : c < 24 := h.hc

theorem keptBy_of_match (hpre : r.Pre) {m m' : MachineData} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hm : Match (r.env m vars ret) S m')
    (hwf : (r.env m vars ret).WF) : KeptBy r S m m' :=
  fun ho hn h ↦ r.bytesAt_kept hpre hm hwf ho h hn

omit [Labels] in
/-- **A step whose writes miss the kept bytes keeps them.** -/
theorem Base.of_kept {c : Nat} {m m' : MachineData} (hB : Base r c m) {S : SState}
    (hk : KeptBy r S m m') (hok : keepOK0 S = true) : Base r c m' := by
  obtain ⟨hc, ⟨i1, i2⟩, s176, s568, s80, s60, sl, sr⟩ := hB
  simp only [keepOK0, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨-, n0⟩, n1⟩, n2⟩, n3⟩, n4⟩, n5⟩, n6⟩ := hok
  have hrl := length_rootsUpTo r (c := c) (by omega)
  have hk' : ∀ {o : Nat} {bs : List UInt8}, ((68 ≤ o ∧ o + bs.length ≤ 72) ∨
      (80 ≤ o ∧ o + bs.length ≤ 88) ∨ (112 ≤ o ∧ o + bs.length ≤ 144)) ∨
      ((184 ≤ o ∧ o + bs.length ≤ 192) ∨ (552 ≤ o ∧ o + bs.length ≤ 560)) ∨
      (10384 ≤ o ∧ o + bs.length ≤ 10576) ∨ (20172 ≤ o ∧ o + bs.length ≤ 28296) →
      BytesAt m.dmem (r.off o) bs → BytesAt m'.dmem (r.off o) bs := fun ho h ↦ by
    refine hk (by omega) ?_ h
    rcases ho with (ho | ho | ho) | (ho | ho) | ho | ho
    · exact Chains.noWriteIn_mono n0 (by omega) (by omega)
    · exact Chains.noWriteIn_mono n1 (by omega) (by omega)
    · exact Chains.noWriteIn_mono n2 (by omega) (by omega)
    · exact Chains.noWriteIn_mono n3 (by omega) (by omega)
    · exact Chains.noWriteIn_mono n4 (by omega) (by omega)
    · exact Chains.noWriteIn_mono n5 (by omega) (by omega)
    · exact Chains.noWriteIn_mono n6 (by omega) (by omega)
  refine ⟨hc, ⟨hk' ?_ i1, hk' ?_ i2⟩, hk' ?_ s176, hk' ?_ s568, hk' ?_ s80, hk' ?_ s60, hk' ?_ sl,
    hk' ?_ sr⟩ <;> (try rw [hrl]) <;> flen

omit [Labels] in
/-- The tree's spills through a step whose writes miss them. -/
theorem Spills.of_kept {c : Nat} {m m' : MachineData} (hT : Spills r c m) {S : SState}
    (hk : KeptBy r S m m') (hok : keepOK S = true) : Spills r c m' := by
  simp only [keepOK, Bool.and_eq_true] at hok
  obtain ⟨⟨-, n1⟩, n2⟩ := hok
  exact ⟨hk (by flen) (by rw [NativeRustc.length_wordBytes]; exact n1) hT.1,
    hk (by flen) (by rw [NativeRustc.length_wordBytes]; exact n2) hT.2⟩

/-- **A block whose writes miss the kept bytes keeps them.** -/
theorem Base.of_block (hpre : r.Pre) {c : Nat} {m m' : MachineData} (hB : Base r c m)
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState} (hm : Match (r.env m vars ret) S m')
    (hwf : (r.env m vars ret).WF) (hok : keepOK0 S = true) : Base r c m' :=
  hB.of_kept (keptBy_of_match hpre hm hwf) hok

/-- The tree's spills through a block whose writes miss them. -/
theorem Spills.of_block (hpre : r.Pre) {c : Nat} {m m' : MachineData} (hT : Spills r c m)
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState} (hm : Match (r.env m vars ret) S m')
    (hwf : (r.env m vars ret).WF) (hok : keepOK S = true) : Spills r c m' :=
  hT.of_kept (keptBy_of_match hpre hm hwf) hok

omit [Labels] in
theorem keepOK0_of {S : SState} (h : keepOK S = true) : keepOK0 S = true := by
  simp only [keepOK, Bool.and_eq_true] at h
  exact h.1.1

omit [Labels] in
theorem frameWrites_of {S : SState} (h : keepOK0 S = true) : Run.frameWrites S = true := by
  simp only [keepOK0, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1

/-- **A block keeping RSP the base** keeps `Keep0`. -/
theorem Keep0.of_block (hpre : r.Pre) {c : Nat} {m m' : MachineData} (hK : Keep0 r c m)
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState} (hm : Match (r.env m vars ret) S m')
    (hwf : (r.env m vars ret).WF) (hok : keepOK0 S = true) (hsp : S.reg .rsp = some (.ptr 0 0)) :
    Keep0 r c m' :=
  ⟨Run.Frame.of_match r hpre hK.1 hm hwf hsp (frameWrites_of hok), hK.2.of_block hpre hm hwf hok⟩

/-- **A block ending in a call** keeps `KeepC0`. -/
theorem KeepC0.of_block (hpre : r.Pre) {c : Nat} {m m' : MachineData} (hK : Keep0 r c m)
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState} (hm : Match (r.env m vars ret) S m')
    (hwf : (r.env m vars ret).WF) (hok : keepOK0 S = true)
    (hsp : S.reg .rsp = some (.ptr 0 (-8))) : KeepC0 r c m' :=
  ⟨Run.AtCall.of_match r hpre hK.1 hm hwf hsp (frameWrites_of hok), hK.2.of_block hpre hm hwf hok⟩

/-- **A block keeping RSP the base** keeps `Keep`. -/
theorem Keep.of_block (hpre : r.Pre) {c : Nat} {m m' : MachineData} (hK : Keep r c m)
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState} (hm : Match (r.env m vars ret) S m')
    (hwf : (r.env m vars ret).WF) (hok : keepOK S = true) (hsp : S.reg .rsp = some (.ptr 0 0)) :
    Keep r c m' :=
  ⟨Run.Frame.of_match r hpre hK.1 hm hwf hsp (frameWrites_of (keepOK0_of hok)),
    hK.2.1.of_block hpre hm hwf (keepOK0_of hok), hK.2.2.of_block hpre hm hwf hok⟩

/-- **A block ending in a call** keeps `KeepC`. -/
theorem KeepC.of_block (hpre : r.Pre) {c : Nat} {m m' : MachineData} (hK : Keep r c m)
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState} (hm : Match (r.env m vars ret) S m')
    (hwf : (r.env m vars ret).WF) (hok : keepOK S = true)
    (hsp : S.reg .rsp = some (.ptr 0 (-8))) : KeepC r c m' :=
  ⟨Run.AtCall.of_match r hpre hK.1 hm hwf hsp (frameWrites_of (keepOK0_of hok)),
    hK.2.1.of_block hpre hm hwf (keepOK0_of hok), hK.2.2.of_block hpre hm hwf hok⟩

/-- `Base` through a call changing scratch. -/
theorem Base.of_call (hpre : r.Pre) {c : Nat} {m m' : MachineData} (hc : r.AtCall m)
    (hB : Base r c m) {a n N : Nat} (ha : Scratch a n) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) : Base r c m' := by
  obtain ⟨hcl, ⟨i1, i2⟩, s176, s568, s80, s60, sl, sr⟩ := hB
  unfold Scratch at ha
  have hrl := length_rootsUpTo r (c := c) (by omega)
  have hk : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 560 ∨
      (10384 ≤ o ∧ o + bs.length ≤ 29352) → BytesAt m.dmem (r.off o) bs →
      BytesAt m'.dmem (r.off o) bs := fun ho h ↦
    r.bytesAt_of_call hpre hc (a := a) (n := n) (by omega) hN hout (by omega) (by omega) h
  refine ⟨hcl, ⟨hk ?_ i1, hk ?_ i2⟩, hk ?_ s176, hk ?_ s568, hk ?_ s80, hk ?_ s60, hk ?_ sl,
    hk ?_ sr⟩ <;> (try rw [hrl]) <;> flen

/-- The tree's spills through a call changing scratch. -/
theorem Spills.of_call (hpre : r.Pre) {c : Nat} {m m' : MachineData} (hc : r.AtCall m)
    (hT : Spills r c m) {a n N : Nat} (ha : Scratch a n) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) : Spills r c m' := by
  unfold Scratch at ha
  have hk : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 184 → BytesAt m.dmem (r.off o) bs →
      BytesAt m'.dmem (r.off o) bs := fun ho h ↦
    r.bytesAt_of_call hpre hc (a := a) (n := n) (by omega) hN hout (by omega) (by omega) h
  exact ⟨hk (by flen) hT.1, hk (by flen) hT.2⟩

/-- **A call changing scratch** keeps `Keep0`. -/
theorem Keep0.of_call (hpre : r.Pre) {c : Nat} {m m' : MachineData} (hK : KeepC0 r c m)
    (hS : Saved m m') (hsp : rspOf m' = rspOf m + 8#64) {a n N : Nat} (ha : Scratch a n)
    (hN : N ≤ finalizeStack) (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) :
    Keep0 r c m' :=
  ⟨r.frame_of_call hpre hK.1 hS hsp (by unfold Scratch at ha; omega) hN hout,
    hK.2.of_call hpre hK.1 ha hN hout⟩

/-- **A call changing scratch** keeps `Keep`. -/
theorem Keep.of_call (hpre : r.Pre) {c : Nat} {m m' : MachineData} (hK : KeepC r c m)
    (hS : Saved m m') (hsp : rspOf m' = rspOf m + 8#64) {a n N : Nat} (ha : Scratch a n)
    (hN : N ≤ finalizeStack) (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) :
    Keep r c m' :=
  ⟨r.frame_of_call hpre hK.1 hS hsp (by unfold Scratch at ha; omega) hN hout,
    hK.2.1.of_call hpre hK.1 ha hN hout, hK.2.2.of_call hpre hK.1 ha hN hout⟩

/-- A fresh symbolic state for the frame: the registers `k`. -/
theorem match_frameS (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {ret : BitVec 64}
    {k : List (Reg64 × Sym)}
    (hk : AllOf (fun p ↦ m.regs.get64 p.1 = p.2.eval (r.env m (fun _ ↦ 0) ret)) k) :
    Match (r.env m (fun _ ↦ 0) ret) (frameS k) m :=
  r.match_frame hpre hF (vars := fun _ ↦ 0) (ret := ret) (known := k) (labels := []) (bounds := [])
    (aliases := []) hk trivial trivial trivial

/-- The frame's symbolic state with a literal word the memory holds. -/
theorem match_litS (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {ret : BitVec 64}
    {k : List (Reg64 × Sym)}
    (hk : AllOf (fun p ↦ m.regs.get64 p.1 = p.2.eval (r.env m (fun _ ↦ 0) ret)) k) {o v : Nat}
    (h : BytesAt m.dmem (r.off o) ((List.range 8).map (byteOf (BitVec.ofNat 64 v)))) :
    Match (r.env m (fun _ ↦ 0) ret) (litS k o v) m :=
  Chains.match_withLit (match_frameS hpre hF hk) rfl h

end

end NativeRustcX64.SphincsVerifyProof.Fors
