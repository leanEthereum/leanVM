module

public import NativeRustcX64.SphincsVerify.Chains.Bytes
public import NativeRustcX64.SphincsVerify.Chains.Exec

/-!
# What the chains keep (x86-64)

Through the chains the inputs, the layer's spills, RBP and R13, the codeword at `3072` and the
ends so far at `28280` stay (`KeepRest`), and, within chain `i`, its spills: `i` at `80`, `16 i`
at `168`, the chain's word at `72` (`ChainSp`). `Keep`: those and the frame's invariant;
`KeepC`: those at a call (RSP 8 below the base). A block whose writes miss the kept bytes keeps
them (`keepOK`, decided on the literal state; `Keep.of_block`, `KeepC.of_block`); a call
changing only scratch bytes (`Scratch`) and its stack keeps them (`Keep.of_call`). The running
of a block of the function (`blk`), its exits' pcs (`pc_cond`, `pc_true`, `pc_false`, `pc_at`),
its labels (`labelAt`), the registers after it (`regIs_reg`, `regIs_ptr`, `regIs_lit`) and
after a call (`RegIs.of_saved`), a fresh state for the frame (`match_frameS`), a literal word the
memory holds (`match_withLit`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Chains

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym NativeRustcX64.Sphincs.SphincsVerify
open LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The kept bytes and registers outside a chain's spills. -/
def KeepRest (r : Run) (l : Nat) (x E : List UInt8) (m : MachineData) : Prop :=
  r.Inputs m ∧ r.LayerSpills l m ∧ Run.RegIs m .rbp (r.off 576) ∧ Run.RegIs m .r13 (r.off 2048) ∧
    BytesAt m.dmem (r.off 3072) x ∧ BytesAt m.dmem (r.off 28280) E

/-- Chain `i`'s spills: `i`, `16 i`, its word `BE32(i)`. -/
def ChainSp (r : Run) (i : Nat) (m : MachineData) : Prop :=
  r.WordAt m 80 i.toUInt64 ∧ r.WordAt m 168 (16 * i).toUInt64 ∧ BytesAt m.dmem (r.off 72) (be32 i.toUInt32)

/-- **What chain `i` keeps**: the frame, the kept bytes and registers, the chain's spills. -/
def Keep (r : Run) (l : Nat) (x E : List UInt8) (i : Nat) (m : MachineData) : Prop :=
  r.Frame m ∧ KeepRest r l x E m ∧ ChainSp r i m

/-- What chain `i` keeps, at a call. -/
def KeepC (r : Run) (l : Nat) (x E : List UInt8) (i : Nat) (m : MachineData) : Prop :=
  r.AtCall m ∧ KeepRest r l x E m ∧ ChainSp r i m

/-- The frame's scratch bytes `a .. a + n` the chains' calls change. -/
def Scratch (a n : Nat) : Prop := (576 ≤ a ∧ a + n ≤ 3072) ∨ (3136 ≤ a ∧ a + n ≤ 20540)

/-- A block's literal state keeps the kept bytes and registers outside a chain's spills: its
writes in the frame below the saved registers (or the slots below it) and off them, RBP and R13
as they were. -/
def restOK (S : SState) : Bool :=
  Run.frameWrites S && Run.noWriteIn S 60 4 && Run.noWriteIn S 88 24 &&
    Run.noWriteIn S 112 32 && Run.noWriteIn S 160 8 && Run.noWriteIn S 176 8 &&
    Run.noWriteIn S 200 24 && Run.noWriteIn S 568 8 && Run.noWriteIn S 3072 64 &&
    Run.noWriteIn S 20540 8764 && S.reg .rbp == some (.ptr 0 576) && S.reg .r13 == some (.ptr 0 2048)

/-- A block's literal state keeps the chain's spills. -/
def chainOK (S : SState) : Bool := Run.noWriteIn S 72 16 && Run.noWriteIn S 168 8

/-- A block's literal state keeps what the chains keep. -/
def keepOK (S : SState) : Bool := restOK S && chainOK S

end

public section

theorem length_pkBytes (w : Nat → UInt64) : (pkBytes w).length = 32 := by
  rw [pkBytes, Native.Keccak.Proof.length_wordsBytes]
  simp

theorem length_sigMemR (r : Run) : (sigMem r.sig).length = 7740 := SigMem.length_sigMem r.w

theorem length_be32 (v : UInt32) : (be32 v).length = 4 := rfl
theorem length_be64 (v : UInt64) : (be64 v).length = 8 := rfl

theorem noWriteIn_mono {S : SState} {o n o' n' : Nat} (h : Run.noWriteIn S o n = true)
    (h1 : o ≤ o') (h2 : o' + n' ≤ o + n) : Run.noWriteIn S o' n' = true := by
  simp only [Run.noWriteIn, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h ⊢
  intro w hw
  rcases h w hw with ⟨h0, h3⟩ | h3
  · exact Or.inl ⟨h0, by omega⟩
  · exact Or.inr h3

theorem allOf_append {α : Type} {P : α → Prop} :
    ∀ {a : List α} {b : List α}, AllOf P a → AllOf P b → AllOf P (a ++ b)
  | [], _, _, hb => hb
  | _ :: _, _, ha, hb => ⟨ha.1, allOf_append ha.2 hb⟩

variable [Labels] {r : Run}

theorem eval_ptr0 (m : MachineData) (vars : Nat → BitVec 64) (ret : BitVec 64) (o : Nat) :
    (Sym.ptr 0 o).eval (r.env m vars ret) = r.off o := by
  simp only [Sym.eval, Run.off, BitVec.ofInt_natCast]
  rfl

/-- **A register a block sets to the frame's byte `o`.** -/
theorem regIs_ptr {m m' : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hm : Match (r.env m vars ret) S m') {y : Reg64} {o : Nat} (h : S.reg y = some (.ptr 0 o)) :
    Run.RegIs m' y (r.off o) := by
  unfold Run.RegIs reg
  rw [hm.regs y _ h, eval_ptr0]

/-- **A register a block sets to a literal.** -/
theorem regIs_lit {env : Env} {m' : MachineData} {S : SState} (hm : Match env S m') {y : Reg64}
    {c : Nat} (h : S.reg y = some (.lit c)) : Run.RegIs m' y (BitVec.ofNat 64 c) := by
  unfold Run.RegIs reg
  rw [hm.regs y _ h]
  rfl

/-- A register holding a raw indirect-call target. -/
theorem regIs_label {env : Env} {m : MachineData} {S : SState} (hm : Match env S m)
    {y : Reg64} {l : Label} (h : S.reg y = some (.label l)) :
    Run.RegIs m y (Labels.label l).toBitVec :=
  hm.regs y _ h

/-- **A register a block keeps.** -/
theorem regIs_reg {m m' : MachineData} {regions : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hm : Match (Env.ofMachine m regions vars ret) S m') {y : Reg64}
    (h : S.reg y = some (.reg y)) {v : BitVec 64} (hv : Run.RegIs m y v) : Run.RegIs m' y v := by
  unfold Run.RegIs reg at *
  rw [hm.regs y _ h]
  exact hv

omit [Labels] in
/-- **A callee-saved register after a call.** -/
theorem RegIs.of_saved {m m' : MachineData} (hS : Saved m m') {y : Reg64}
    (hy : calleeSaved y = true) {v : BitVec 64} (h : Run.RegIs m y v) : Run.RegIs m' y v := by
  unfold Run.RegIs reg at *
  rw [hS.1 y hy]
  exact h

/-- A register set to a literal: its number. -/
theorem toNat_of_lit {env : Env} {m' : MachineData} {S : SState} (hm : Match env S m') {y : Reg64}
    {c : Nat} (h : S.reg y = some (.lit c)) (hc : c < 2 ^ 64) : (reg m' y).toNat = c := by
  have := hm.regs y _ h
  unfold reg
  rw [this]
  exact Nat.mod_eq_of_lt hc

theorem known_ptr {m : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64} {y : Reg64} {o : Nat}
    (h : Run.RegIs m y (r.off o)) : m.regs.get64 y = (Sym.ptr 0 o).eval (r.env m vars ret) := by
  rw [eval_ptr0]
  exact h

theorem known_lit {m : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64} {y : Reg64} {c : Nat}
    (h : Run.RegIs m y (BitVec.ofNat 64 c)) : m.regs.get64 y = (Sym.lit c).eval (r.env m vars ret) :=
  h

/-- **A fresh symbolic state for the frame**: the registers `k` and `keptK`. -/
theorem match_frameS (hpre : r.Pre) {l : Nat} {x E : List UInt8} {m : MachineData}
    (hF : r.Frame m) (hK : KeepRest r l x E m) {ret : BitVec 64} {k : List (Reg64 × Sym)}
    (hk : AllOf (fun p ↦ m.regs.get64 p.1 = p.2.eval (r.env m (fun _ ↦ 0) ret)) k) :
    Match (r.env m (fun _ ↦ 0) ret) (frameS k) m := by
  have hk2 : AllOf (fun p : Reg64 × Sym ↦ m.regs.get64 p.1 = p.2.eval (r.env m (fun _ ↦ 0) ret))
      keptK := by
    unfold keptK
    exact ⟨known_ptr hK.2.2.1, known_ptr hK.2.2.2.1, trivial⟩
  exact r.match_frame hpre hF (vars := fun _ ↦ 0) (ret := ret) (known := k ++ keptK) (labels := [])
    (bounds := []) (aliases := []) (allOf_append hk hk2) trivial trivial trivial

/-- **A literal word the memory holds**, as a write of the symbolic state. -/
theorem match_withLit {m : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hm : Match (r.env m vars ret) S m) (hS : S.mem = []) {o n c : Nat}
    (h : BytesAt m.dmem (r.off o) ((List.range n).map (byteOf (BitVec.ofNat 64 c)))) :
    Match (r.env m vars ret) { S with mem := [⟨0, o, n, .lit c⟩] } m :=
  Match.withWrite hm hS (b := r.base) (sz := frameRegion) rfl fun i hi ↦ by
    have := h i (by simp; omega)
    rw [Run.off_add] at this
    show m.dmem.get? (r.off (o + i)) = _
    rw [this]
    simp [Sym.eval]

/-! ## Kept -/

/-- **A block whose writes miss the kept bytes keeps them.** -/
theorem KeepRest.of_block (hpre : r.Pre) {l : Nat} {x E : List UInt8} (hx : x.length = 64)
    (hE : E.length ≤ 1024) {m m' : MachineData} (hK : KeepRest r l x E m)
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState} (hm : Match (r.env m vars ret) S m')
    (hwf : (r.env m vars ret).WF) (hok : restOK S = true) : KeepRest r l x E m' := by
  obtain ⟨⟨i1, i2⟩, ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩, hbp, h13, hxa, hEa⟩ := hK
  simp only [restOK, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, n0⟩, n1⟩, n2⟩, n3⟩, n4⟩, n5⟩, n6⟩, n7⟩, n8⟩, hrbp⟩, hr13⟩ := hok
  have hk : ∀ {o : Nat} {bs : List UInt8}, ((60 ≤ o ∧ o + bs.length ≤ 64) ∨
      (88 ≤ o ∧ o + bs.length ≤ 112) ∨ (112 ≤ o ∧ o + bs.length ≤ 144)) ∨
      ((160 ≤ o ∧ o + bs.length ≤ 168) ∨ (176 ≤ o ∧ o + bs.length ≤ 184) ∨
      (200 ≤ o ∧ o + bs.length ≤ 224)) ∨ ((568 ≤ o ∧ o + bs.length ≤ 576) ∨
      (3072 ≤ o ∧ o + bs.length ≤ 3136)) ∨ (20540 ≤ o ∧ o + bs.length ≤ 29304) →
      BytesAt m.dmem (r.off o) bs → BytesAt m'.dmem (r.off o) bs := fun ho h ↦ by
    refine r.bytesAt_kept hpre hm hwf (by omega) h ?_
    rcases ho with (ho | ho | ho) | (ho | ho | ho) | (ho | ho) | ho
    · exact noWriteIn_mono n0 (by omega) (by omega)
    · exact noWriteIn_mono n1 (by omega) (by omega)
    · exact noWriteIn_mono n2 (by omega) (by omega)
    · exact noWriteIn_mono n3 (by omega) (by omega)
    · exact noWriteIn_mono n4 (by omega) (by omega)
    · exact noWriteIn_mono n5 (by omega) (by omega)
    · exact noWriteIn_mono n6 (by omega) (by omega)
    · exact noWriteIn_mono n7 (by omega) (by omega)
    · exact noWriteIn_mono n8 (by omega) (by omega)
  refine ⟨⟨hk ?_ i1, hk ?_ i2⟩, ⟨hk ?_ s1, hk ?_ s2, hk ?_ s3, hk ?_ s4, hk ?_ s5, hk ?_ s6,
    hk ?_ s7, hk ?_ s8, hk ?_ s9, hk ?_ s10⟩, regIs_ptr hm hrbp, regIs_ptr hm hr13, hk ?_ hxa,
    hk ?_ hEa⟩ <;>
    (try simp only [length_pkBytes, length_sigMemR, NativeRustc.length_wordBytes, length_be32,
      length_be64, hx]) <;> omega

/-- The chain's spills through a block whose writes miss them. -/
theorem ChainSp.of_block (hpre : r.Pre) {i : Nat} {m m' : MachineData} (hC : ChainSp r i m)
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState} (hm : Match (r.env m vars ret) S m')
    (hwf : (r.env m vars ret).WF) (hok : chainOK S = true) : ChainSp r i m' := by
  simp only [chainOK, Bool.and_eq_true] at hok
  obtain ⟨n1, n3⟩ := hok
  exact ⟨r.bytesAt_kept hpre hm hwf (by simp [NativeRustc.length_wordBytes]) hC.1
      (noWriteIn_mono n1 (by omega) (by simp [NativeRustc.length_wordBytes])),
    r.bytesAt_kept hpre hm hwf (by simp [NativeRustc.length_wordBytes]) hC.2.1
      (noWriteIn_mono n3 (by omega) (by simp [NativeRustc.length_wordBytes])),
    r.bytesAt_kept hpre hm hwf (by simp [length_be32]) hC.2.2
      (noWriteIn_mono n1 (by omega) (by simp [length_be32]))⟩

omit [Labels] in
theorem restOK_of_keepOK {S : SState} (h : keepOK S = true) : restOK S = true := by
  simp only [keepOK, Bool.and_eq_true] at h
  exact h.1

omit [Labels] in
theorem chainOK_of_keepOK {S : SState} (h : keepOK S = true) : chainOK S = true := by
  simp only [keepOK, Bool.and_eq_true] at h
  exact h.2

omit [Labels] in
theorem frameWrites_of_restOK {S : SState} (h : restOK S = true) : Run.frameWrites S = true := by
  simp only [restOK, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1.1

/-- **A block keeping RSP the base** keeps what chain `i` keeps. -/
theorem Keep.of_block (hpre : r.Pre) {l : Nat} {x E : List UInt8} (hx : x.length = 64)
    (hE : E.length ≤ 1024) {i : Nat} {m m' : MachineData} (hK : Keep r l x E i m)
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState} (hm : Match (r.env m vars ret) S m')
    (hwf : (r.env m vars ret).WF) (hok : keepOK S = true) (hsp : S.reg .rsp = some (.ptr 0 0)) :
    Keep r l x E i m' := by
  exact ⟨Run.Frame.of_match r hpre hK.1 hm hwf hsp (frameWrites_of_restOK (restOK_of_keepOK hok)),
    hK.2.1.of_block hpre hx hE hm hwf (restOK_of_keepOK hok),
    hK.2.2.of_block hpre hm hwf (chainOK_of_keepOK hok)⟩

/-- **A block ending in a call** (RSP 8 below the base) keeps what chain `i` keeps. -/
theorem KeepC.of_block (hpre : r.Pre) {l : Nat} {x E : List UInt8} (hx : x.length = 64)
    (hE : E.length ≤ 1024) {i : Nat} {m m' : MachineData} (hK : Keep r l x E i m)
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState} (hm : Match (r.env m vars ret) S m')
    (hwf : (r.env m vars ret).WF) (hok : keepOK S = true) (hsp : S.reg .rsp = some (.ptr 0 (-8))) :
    KeepC r l x E i m' := by
  exact ⟨Run.AtCall.of_match r hpre hK.1 hm hwf hsp
      (frameWrites_of_restOK (restOK_of_keepOK hok)),
    hK.2.1.of_block hpre hx hE hm hwf (restOK_of_keepOK hok),
    hK.2.2.of_block hpre hm hwf (chainOK_of_keepOK hok)⟩

/-- **A call changing scratch bytes** keeps what chain `i` keeps. -/
theorem Keep.of_call (hpre : r.Pre) {l : Nat} {x E : List UInt8} (hx : x.length = 64)
    (hE : E.length ≤ 1024) {i : Nat} {m m' : MachineData} (hK : KeepC r l x E i m)
    (hS : Saved m m') (hsp : rspOf m' = rspOf m + 8#64) {a n N : Nat} (ha : Scratch a n)
    (hN : N ≤ finalizeStack) (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) :
    Keep r l x E i m' := by
  obtain ⟨hc, ⟨⟨i1, i2⟩, ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩, hbp, h13, hxa, hEa⟩,
    ⟨c1, c2, c3⟩⟩ := hK
  have ha' : a + n ≤ 29336 := by unfold Scratch at ha; omega
  have hk : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 576 ∨
      (3072 ≤ o ∧ o + bs.length ≤ 3136) ∨ (20540 ≤ o ∧ o + bs.length ≤ 29304) →
      BytesAt m.dmem (r.off o) bs → BytesAt m'.dmem (r.off o) bs := fun ho h ↦
    r.bytesAt_of_call hpre hc (by omega) hN hout (by omega) (by unfold Scratch at ha; omega) h
  refine ⟨r.frame_of_call hpre hc hS hsp ha' hN hout, ⟨⟨hk ?_ i1, hk ?_ i2⟩, ⟨hk ?_ s1, hk ?_ s2,
    hk ?_ s3, hk ?_ s4, hk ?_ s5, hk ?_ s6, hk ?_ s7, hk ?_ s8, hk ?_ s9, hk ?_ s10⟩,
    RegIs.of_saved hS rfl hbp, RegIs.of_saved hS rfl h13, hk ?_ hxa, hk ?_ hEa⟩,
    ⟨hk ?_ c1, hk ?_ c2, hk ?_ c3⟩⟩ <;>
    (try simp only [length_pkBytes, length_sigMemR, NativeRustc.length_wordBytes, length_be32,
      length_be64, hx]) <;> omega

/-! ## Running blocks -/

theorem pc_cond {env : Env} {c : SBool} {l : Label} {next : Int64} {st : MachineState}
    (h : PcOk env (.cond c l) next st) : st.pc = if c.eval env then Labels.label l else next := h

theorem pc_true {env : Env} {l : Label} {next : Int64} {st : MachineState}
    (h : PcOk env (.cond (.lit true) l) next st) : st.pc = Labels.label l := h

theorem pc_false {env : Env} {l : Label} {next : Int64} {st : MachineState}
    (h : PcOk env (.cond (.lit false) l) next st) : st.pc = next := h

end

public section
variable [Host]

/-- **A block of the function** run from directive `j`, then `cont` from where it ends. -/
theorem blk (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) {ds : List Directive}
    {j : Nat} (hb : ds.IsInfixAt Sphincs.SphincsVerify.code j) (hne : ds ≠ []) {env : Env}
    {S S' : SState} {x : Exit} (hx : exec ds S = some (S', x)) (hwf : env.WF)
    (hret : ∀ l, x = .call l → env.ret = (r.pc (j + ds.length)).toBitVec) {m : MachineData}
    (hm : Match env S m) {R : MachineState → Prop}
    (cont : ∀ st, Match env S' st.data → PcOk env x (r.pc (j + ds.length)) st →
      Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m, r.pc j⟩ :=
  exec_then (hb.trans hp.1 hne) hx hwf
    (fun l h ↦ (hret l h).trans (by rw [Run.pc, Nat.add_assoc])) hm fun st h1 h2 ↦
    cont st h1 (by rw [Run.pc, ← Nat.add_assoc]; exact h2)

/-- A state at a known pc. -/
theorem pc_at {R : MachineState → Prop} {st : MachineState} {a : Int64} (h : st.pc = a)
    (k : Eventually (step1 Host.exe) R ⟨st.data, a⟩) : Eventually (step1 Host.exe) R st := by
  obtain ⟨d, pc⟩ := st
  subst h
  exact k

/-- **A label of the function** is the address of the block it starts. -/
theorem labelAt (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) {b : List Directive}
    {j : Nat} (hb : b.IsInfixAt Sphincs.SphincsVerify.code j) {l : Label} {b' : List Directive}
    (h : b = .label l :: b') : Labels.label l = r.pc j := by
  subst h
  exact hp.label (List.IsInfixAt.cons hb).1

end

end NativeRustcX64.SphincsVerifyProof.Chains
