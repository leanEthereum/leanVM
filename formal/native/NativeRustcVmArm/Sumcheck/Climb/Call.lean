module

public import NativeRustcVmArm.Code.Vm.Climb.Names
public import NativeRustcVmArm.Code.Vm.HashPair.Names
public import NativeRustcVmArm.Sumcheck.Climb.Entry

/-!
# `climb`'s loop: one level up to `hash_pair`'s return

From the loop head with `l` levels climbed (`Inv`), `b5` (level `4 l ≤ 124`, no zero sibling),
`b6` (the sibling `P[l]` into the frame at `32`), the side by the position's low bit (`b2`, or
`b7`, `b9`), `b3`'s call of `hash_pair` on the accumulator and the sibling: on its return the
frame holds `climbTo (l + 1)`'s digest at `64` (`Called`, `call_spec`).
-/

namespace NativeRustcVmArm.Sumcheck.Climb

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Climb
open NativeVm.Model LeanVM.Protocol NativeRustcVm.Sumcheck

@[expose] public section

/-- **After `hash_pair`** on level `l`: the frame as in `Frame`, the new digest at `64`, the
loop's registers. -/
structure Called (m0 : MachineData) (N : Digest) (P : Array Digest) (l : Nat) (m : MachineData) :
    Prop where
  sp : m.regs.SP.toBitVec = fr m0
  x19 : (m.regs.getXReg .X19).toBitVec = outAt m0
  hashed : NativeRustcVm.WordsAt m.dmem (fr m0 + BitVec.ofNat 64 64)
    (climbTo N m0.regs.X2 P (l + 1)).1.toList
  slots : NativeRustcVm.WordsAt m.dmem (fr m0 + BitVec.ofNat 64 96) (slotWords m0)
  regs : ∀ r ∈ outer, m.regs.getXReg r = m0.regs.getXReg r
  same : SameOutside m0.dmem m.dmem (InRange (stackBelow m0 climbStack) climbStack)
  kept : Kept m0.dmem m.dmem
  lt : l < P.size
  x20 : (m.regs.getXReg .X20).toNat = P.size - l
  x21 : m.regs.getXReg .X21 = (climbTo N m0.regs.X2 P l).2
  x22 : (m.regs.getXReg .X22).toNat = 4 * l
  x23 : (m.regs.getXReg .X23).toBitVec = m0.regs.X3.toBitVec + BitVec.ofNat 64 (32 * l + 16)

end

public section

variable [Host] {N : Digest} {P : Array Digest} {m0 : MachineData} {k : Nat}

/-- The sibling of level `l`. -/
def sib (m0 : MachineData) (l : Nat) : BitVec 64 := m0.regs.X3.toBitVec + BitVec.ofNat 64 (32 * l)

/-- The loop head's environment: the frame and the sibling. -/
def env1 (m0 : MachineData) (l : Nat) (m : MachineData) : Env :=
  Env.ofMachine m [(fr m0, 144), (sib m0 l, 32)]

/-- The path's bytes are apart from `climb`'s stack and do not wrap. -/
theorem path_geo (hpre : ClimbPre N P m0) {l : Nat} (hl : l < P.size) :
    (sib m0 l).toNat = m0.regs.X3.toBitVec.toNat + 32 * l ∧
      m0.regs.X3.toBitVec.toNat + 32 * P.size ≤ 2 ^ 64 ∧
      (m0.regs.X3.toBitVec.toNat + 32 * P.size ≤ m0.regs.SP.toNat - 912 ∨
        m0.regs.SP.toNat ≤ m0.regs.X3.toBitVec.toNat) := by
  have g := geo_of hpre
  have ⟨_, _, _, _, _, _, _⟩ := g
  have ⟨_, _, _, hsz, _, _, _, hnw, _, _, _, hap, _⟩ := hpre
  rw [← hsz] at hnw hap
  unfold NoWrap at hnw
  unfold Apart at hap
  rw [g.stk, climbStack_eq] at hap
  refine ⟨NativeRustcVm.toNat_add_ofNat (by omega), hnw, by omega⟩

/-- The sibling's words at the loop head. -/
theorem sib_words (hpre : ClimbPre N P m0) {l : Nat} (hl : l < P.size) {m : MachineData}
    (hsame : SameOutside m0.dmem m.dmem (InRange (stackBelow m0 climbStack) climbStack)) :
    NativeRustcVm.WordsAt m.dmem (sib m0 l) P[l].toList := by
  have g := geo_of hpre
  have ⟨_, _, _, _, _, _, _⟩ := g
  have ⟨h1, h2, h3⟩ := path_geo hpre hl
  have hw : NativeRustcVm.WordsAt m0.dmem (sib m0 l) P[l].toList :=
    wordsAt_path hpre.2.2.2.2.2.1 hl
  refine NativeRustcVm.BytesAt.of_sameOutside hw hsame fun i hi hin ↦ ?_
  rw [NativeRustcVm.length_wordsBytes] at hi
  simp only [Vector.length_toList] at hi
  have hin' := (Sym.inRange_iff (by rw [g.stk, climbStack_eq]; omega)).mp hin
  rw [g.stk, climbStack_eq, NativeRustcVm.toNat_add_ofNat (by rw [h1]; omega), h1] at hin'
  omega

/-- The loop head's environment is well formed. -/
theorem wf_env1 (hpre : ClimbPre N P m0) {l : Nat} {m : MachineData} (hinv : Inv m0 N P l m) :
    (env1 m0 l m).WF := by
  have g := geo_of hpre
  have ⟨_, _, _, _, _, _, _⟩ := g
  have hl := hinv.lt
  have ⟨hs1, hs2, hs3⟩ := path_geo hpre hl
  have hw := sib_words hpre hl hinv.frame.same
  have hmS : Mapped m.dmem (sib m0 l) 32 := by
    have := NativeRustcVm.WordsAt.mapped hw
    simp only [Vector.length_toList] at this
    exact this
  refine Env.wf_of ⟨⟨mapped_fr hpre hinv.frame.kept, by show _ + 144 ≤ _; rw [g.fr]; omega⟩,
      ⟨hmS, by show _ + 32 ≤ _; rw [hs1]; omega⟩, trivial⟩
    (List.Pairwise.cons ?_ (List.pairwise_singleton _ _))
  simp only [List.mem_singleton, forall_eq]
  show _ ∨ _
  rw [g.fr, hs1]
  omega

/-- The loop head's state. -/
theorem match_headS (hpre : ClimbPre N P m0) {l : Nat} {m : MachineData}
    (hinv : Inv m0 N P l m) : Match (env1 m0 l m) headS m := by
  have g := geo_of hpre
  have ⟨_, _, _, _, _, _, _⟩ := g
  refine match_ofMachine ⟨rfl, fun _ ↦ by rw [g.fr]; omega, rfl, by simp, trivial⟩
    (by simp [Sym.eval, hinv.frame.sp]) ⟨?_, trivial⟩ trivial trivial trivial
  show (m.regs.getXReg .X23).toBitVec = (env1 m0 l m).base 1 + BitVec.ofInt 64 16
  rw [hinv.x23, show (env1 m0 l m).base 1 = sib m0 l from rfl, sib, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  omega

/-- The geometry of the frame against the stacks. -/
theorem fr_geo (hpre : ClimbPre N P m0) :
    (fr m0).toNat = m0.regs.SP.toNat - 144 ∧ (stackBelow m0 climbStack).toNat =
      m0.regs.SP.toNat - 912 ∧ 912 ≤ m0.regs.SP.toNat ∧ m0.regs.SP.toNat < 2 ^ 64 ∧
      m0.regs.SP.toNat % 16 = 0 := by
  have g := geo_of hpre
  exact ⟨g.fr, g.stk, g.le, g.lt, g.al⟩

/-- **The call and its return**: from the call of `hash_pair` on the accumulator and the sibling
(swapped when `sw`), the digest of `climbTo (l + 1)` at `64`. -/
theorem after_call (hhp : Spec (Labels.label NativeRustcVmArm.Vm.HashPair.entryLabel) HashPairPre HashPairPost)
    (hpre : ClimbPre N P m0) {l : Nat} {m : MachineData} (hinv : Inv m0 N P l m)
    (sw : Bool) {S : SState} {st : MachineState}
    (hm : Match (env1 m0 l m) S st.data)
    (hmem : S.mem = (after b6 (after b5 headS)).mem) (hsp : S.sp = .ptr 0 0)
    (hx0 : S.reg .X0 = some (.ptr 0 64))
    (hx1 : S.reg .X1 = some (.ptr 0 ((if sw then 32 else 0 : Nat) : Int)))
    (hx2 : S.reg .X2 = some (.ptr 0 ((if sw then 0 else 32 : Nat) : Int)))
    (hregs : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23] ++ outer, S.reg r = headS.reg r)
    (hclimb : (climbTo N m0.regs.X2 P (l + 1)).1 =
      if sw then hashPair (P[l]'hinv.lt) (climbTo N m0.regs.X2 P l).1
      else hashPair (climbTo N m0.regs.X2 P l).1 (P[l]'hinv.lt))
    (hpc : PcOk (env1 m0 l m) (.call NativeRustcVmArm.Vm.HashPair.entryLabel)
      (Host.addrOf (k + NativeRustcVmArm.Vm.Climb.b4Offset)) st) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Climb.b4Offset) ∧ Called m0 N P l st.data) st := by
  have hf := hinv.frame
  have ⟨gfr, gstk, gle, glt, gal⟩ := fr_geo hpre
  have hl := hinv.lt
  have hwf := wf_env1 hpre hinv
  have hm0 := match_headS hpre hinv
  have hb0 : (env1 m0 l m).base 0 = fr m0 := rfl
  have hb1 : (env1 m0 l m).base 1 = sib m0 l := rfl
  have hfrN : ∀ o, o ≤ 144 → (fr m0 + BitVec.ofNat 64 o).toNat = (fr m0).toNat + o :=
    fun o ho ↦ NativeRustcVm.toNat_add_ofNat (by omega)
  -- The block's writes: the sibling at `32` of the frame.
  have hW : ∀ p, Written (env1 m0 l m) S p →
      (fr m0).toNat + 32 ≤ p.toNat ∧ p.toNat < (fr m0).toNat + 64 :=
    fun p h ↦ Written.toNat (r := 0) rfl (by rw [hmem, after_eq run_b6]; decide +kernel) h
  have hst : ∀ p, ¬((fr m0).toNat + 32 ≤ p.toNat ∧ p.toNat < (fr m0).toNat + 64) →
      st.data.dmem.get? p = m.dmem.get? p :=
    fun p hp ↦ hm.get?_mem0 hwf fun h ↦ hp (hW p h)
  have hkept : Kept m0.dmem st.data.dmem := fun p h ↦ hm.kept hwf p (hf.kept p h)
  have hacc : NativeRustcVm.WordsAt st.data.dmem (fr m0) (climbTo N m0.regs.X2 P l).1.toList :=
    NativeRustcVm.BytesAt.of_sameOutside hf.acc (R := fun p ↦
      (fr m0).toNat + 32 ≤ p.toNat ∧ p.toNat < (fr m0).toNat + 64) (fun p hp ↦ hst p hp)
      fun i hi ↦ by
        rw [NativeRustcVm.length_wordsBytes] at hi
        simp only [Vector.length_toList] at hi
        rw [hfrN i (by omega)]
        omega
  have hsibw : NativeRustcVm.WordsAt st.data.dmem (fr m0 + BitVec.ofNat 64 32) P[l].toList := by
    have hsw := sib_words hpre hl hf.same
    have hw : ∀ i < 4, ∀ j < 8,
        findWrite 0 (32 + 8 * i + j) S.mem = some (.load 1 (8 * i) 8, j) := by
      rw [hmem, after_eq run_b6]; decide +kernel
    rw [NativeRustcVm.wordsAt_iff]
    intro i hi
    simp only [Vector.length_toList] at hi
    have := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm (r := 0) (o := 32 + 8 * i) rfl
      (by omega) (hw i hi)
    rw [show (Sym.load 1 (8 * i) 8).eval (env1 m0 l m) = (env1 m0 l m).load 1 (8 * i) 8 from rfl,
      load_word (by rw [hb1]; exact hsw.getElem (i := i) (by simpa using hi))] at this
    rw [NativeRustcVm.addr_add_add]
    exact this
  -- Registers.
  have hreg : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23] ++ outer,
      st.data.regs.getXReg r = m.regs.getXReg r := by
    intro r hr
    have h0 := hregs r hr
    cases hS : headS.reg r with
    | none =>
      exfalso
      simp only [outer, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact absurd hS (by decide)
    | some v => exact Match.reg_eq hm0 hm hS (h0.trans hS)
  have hsp : st.data.regs.SP.toBitVec = fr m0 := by
    rw [hm.sp, hsp]; simp [Sym.eval, hb0]
  have hX : ∀ (r : XReg) (o : Nat), S.reg r = some (.ptr 0 o) →
      st.data.regs.getXReg r = UInt64.ofBitVec (fr m0 + BitVec.ofNat 64 o) := by
    intro r o h
    apply UInt64.toBitVec_inj.mp
    rw [hm.regs r _ h]
    simp [Sym.eval, hb0]
  have hx0' : st.data.regs.X0 = _ := hX .X0 64 hx0
  have hx1' : st.data.regs.X1 = _ := hX .X1 _ hx1
  have hx2' : st.data.regs.X2 = _ := hX .X2 _ hx2
  have hspN : st.data.regs.SP.toNat = (fr m0).toNat := by
    show st.data.regs.SP.toBitVec.toNat = _; rw [hsp]
  have hrc := hpre.2.1
  have hrcN : rcAddr.toNat + 192 ≤ m0.regs.SP.toNat - 912 ∨
      m0.regs.SP.toNat ≤ rcAddr.toNat := by
    have := hrc.2.2
    unfold Apart at this
    rw [gstk, climbStack_eq] at this
    omega
  have hrcNw : rcAddr.toNat + 192 ≤ 2 ^ 64 := hrc.2.1
  have hmapfr : Mapped st.data.dmem (fr m0) 144 := mapped_fr hpre hkept
  have hspst : st.data.regs.SP.toBitVec = m0.regs.SP.toBitVec - BitVec.ofNat 64 144 := hsp
  have hps : hashPairStack = 768 := rfl
  have habove : ∀ o, o + 32 ≤ 144 →
      Apart (fr m0 + BitVec.ofNat 64 o) 32 (stackBelow st.data hashPairStack) hashPairStack :=
    fun o ho ↦ apart_above (by rw [hfrN o (by omega), hspN]; omega) (by rw [hspN, hps]; omega)
  have hrcst : ∀ p, InRange rcAddr 192 p → st.data.dmem.get? p = m0.dmem.get? p := by
    intro p hp
    rw [Sym.inRange_iff hrcNw] at hp
    rw [hst p (by omega), hf.same p (by
      rw [Sym.inRange_iff (by rw [gstk, climbStack_eq]; omega), gstk, climbStack_eq]; omega)]
  refine call_then hpc hhp ?pre fun st' hpc' hpost ↦ ?_
  case pre =>
    simp only [HashPairPre, hx0', hx1', hx2', UInt64.toBitVec_ofBitVec]
    refine ⟨StackOk.sub hpre.1 hspst (by decide) (by decide) hkept,
      RcAt.sub hrc hspst (by decide) (by rw [climbStack_eq]; exact gle) hrcst,
      NativeRustcVm.Mapped.sub hmapfr (by split <;> omega), ?_,
      NativeRustcVm.Mapped.sub hmapfr (by split <;> omega), ?_,
      NativeRustcVm.Mapped.sub hmapfr (by omega), ?_, habove _ (by split <;> omega), habove _ (by split <;> omega),
      habove _ (by omega), ?_⟩
    · show _ + 32 ≤ _; split <;> (rw [hfrN _ (by omega)]; omega)
    · show _ + 32 ≤ _; split <;> (rw [hfrN _ (by omega)]; omega)
    · show _ + 32 ≤ _; rw [hfrN _ (by omega)]; omega
    · show _ ∨ _; rw [hfrN _ (by omega)]; omega
  simp only [HashPairPost, hx0', hx1', hx2', UInt64.toBitVec_ofBitVec] at hpost
  obtain ⟨hhash, hsame', hsaved⟩ := hpost
  have hout : ∀ p, InRange (fr m0 + BitVec.ofNat 64 64) 32 p ∨
      InRange (stackBelow st.data hashPairStack) hashPairStack p →
      (fr m0).toNat + 64 ≤ p.toNat ∧ p.toNat < (fr m0).toNat + 96 ∨
        (fr m0).toNat - 768 ≤ p.toNat ∧ p.toNat < (fr m0).toNat := by
    intro p hp
    have hsb : (stackBelow st.data hashPairStack).toNat = (fr m0).toNat - 768 :=
      by rw [toNat_stackBelow (by rw [hspN, hps]; omega), hspN, hps]
    rcases hp with hp | hp
    · rw [Sym.inRange_iff (by rw [hfrN _ (by omega)]; omega), hfrN _ (by omega)] at hp
      omega
    · rw [Sym.inRange_iff (by rw [hsb, hps]; omega), hsb, hps] at hp
      omega
  have hst' : ∀ p, ¬((fr m0).toNat + 64 ≤ p.toNat ∧ p.toNat < (fr m0).toNat + 96 ∨
      (fr m0).toNat - 768 ≤ p.toNat ∧ p.toNat < (fr m0).toNat) →
      st'.data.dmem.get? p = st.data.dmem.get? p :=
    fun p hp ↦ hsame' p fun h ↦ hp (hout p h)
  have hreg' : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23] ++ outer,
      st'.data.regs.getXReg r = m.regs.getXReg r := by
    intro r hr
    rw [hsaved.1 r (by
      simp only [outer, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)]
    exact hreg r hr
  refine Eventually.done _ ⟨hpc', ?_, ?_, ?_, ?_, ?_, ?_, ?_, hl, ?_, ?_, ?_, ?_⟩
  · show st'.data.regs.SP.toBitVec = _
    rw [hsaved.2.1]; exact hsp
  · rw [hreg' .X19 (by simp)]; exact hf.x19
  · rw [hclimb]
    have hacc0 : NativeRustcVm.WordsAt st.data.dmem (fr m0 + BitVec.ofNat 64 0)
        (climbTo N m0.regs.X2 P l).1.toList := by rw [NativeRustcVm.addr_add_zero]; exact hacc
    cases sw
    · exact hhash _ _ (by simpa using hacc0) (by simpa using hsibw)
    · exact hhash _ _ (by simpa using hsibw) (by simpa using hacc0)
  · refine NativeRustcVm.BytesAt.of_sameOutside hf.slots (R := fun p ↦
      ((fr m0).toNat + 64 ≤ p.toNat ∧ p.toNat < (fr m0).toNat + 96 ∨
        (fr m0).toNat - 768 ≤ p.toNat ∧ p.toNat < (fr m0).toNat) ∨
      ((fr m0).toNat + 32 ≤ p.toNat ∧ p.toNat < (fr m0).toNat + 64))
      (fun p hp ↦ by
        rw [hst' p fun h ↦ hp (Or.inl h), hst p fun h ↦ hp (Or.inr h)]) fun i hi ↦ ?_
    rw [NativeRustcVm.length_wordsBytes] at hi
    simp only [slotWords, List.length_cons, List.length_nil] at hi
    rw [NativeRustcVm.addr_add_add, hfrN _ (by omega)]
    omega
  · intro r hr
    rw [hreg' r (by simp [hr])]; exact hf.regs r hr
  · intro p hp
    have hp' : ¬(m0.regs.SP.toNat - 912 ≤ p.toNat ∧ p.toNat < m0.regs.SP.toNat) := by
      rw [Sym.inRange_iff (by rw [gstk, climbStack_eq]; omega), gstk, climbStack_eq] at hp
      omega
    rw [hst' p (by omega), hst p (by omega)]
    exact hf.same p hp
  · exact fun p h ↦ hsaved.2.2 p (hkept p h)
  · rw [hreg' .X20 (by simp)]; exact hinv.x20
  · rw [hreg' .X21 (by simp)]; exact hinv.x21
  · rw [hreg' .X22 (by simp)]; exact hinv.x22
  · rw [hreg' .X23 (by simp)]; exact hinv.x23

/-- **One level, up to `hash_pair`'s return.** -/
theorem call_spec (hp : Placed code k)
    (hhp : Spec (Labels.label NativeRustcVmArm.Vm.HashPair.entryLabel) HashPairPre HashPairPost)
    (hpre : ClimbPre N P m0) {l : Nat} {m : MachineData} (hinv : Inv m0 N P l m) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Climb.b4Offset) ∧ Called m0 N P l st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.Climb.b5Offset)⟩ := by
  have hl := hinv.lt
  have hP : P.size = m0.regs.X4.toNat := hpre.2.2.2.1
  have hwf := wf_env1 hpre hinv
  have hm0 := match_headS hpre hinv
  have hk5 : b5.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Climb.b5Offset) := b5_in_code.trans hp.1 (by simp [b5])
  have hk6 : b6.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Climb.b6Offset) := b6_in_code.trans hp.1 (by simp [b6])
  have hk2 : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Climb.b2Offset) := b2_in_code.trans hp.1 (by simp [b2])
  have hk3 : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Climb.b3Offset) := b3_in_code.trans hp.1 (by simp [b3])
  have hk7 : b7.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Climb.b7Offset) := b7_in_code.trans hp.1 (by simp [b7])
  have hk9 : b9.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Climb.b9Offset) := b9_in_code.trans hp.1 (by simp [b9])
  have hl2 : Labels.label NativeRustcVmArm.Vm.Climb.label_2 = Host.addrOf (k + NativeRustcVmArm.Vm.Climb.b2Offset) := hp.label (j := NativeRustcVmArm.Vm.Climb.b2Offset) NativeRustcVmArm.Vm.Climb.label_2_at
  have hl3 : Labels.label NativeRustcVmArm.Vm.Climb.label_3 = Host.addrOf (k + NativeRustcVmArm.Vm.Climb.b3Offset) := hp.label (j := NativeRustcVmArm.Vm.Climb.b3Offset) NativeRustcVmArm.Vm.Climb.label_3_at
  have hl7 : Labels.label NativeRustcVmArm.Vm.Climb.label_7 = Host.addrOf (k + NativeRustcVmArm.Vm.Climb.b9Offset) := hp.label (j := NativeRustcVmArm.Vm.Climb.b9Offset) NativeRustcVmArm.Vm.Climb.label_7_at
  have h4l : 4 * l ≤ 124 := by
    have h32 : m0.regs.X4.toNat ≤ 32 := hpre.2.2.1
    omega
  have hx22 : (env1 m0 l m).regs .X22 = BitVec.ofNat 64 (4 * l) := by
    show (m.regs.getXReg .X22).toBitVec = _
    apply BitVec.eq_of_toNat_eq
    rw [UInt64.toNat_toBitVec, hinv.x22, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx21 : (env1 m0 l m).regs .X21 = (climbTo N m0.regs.X2 P l).2.toBitVec := by
    show (m.regs.getXReg .X21).toBitVec = _
    rw [hinv.x21]
  refine exec_then hk5 run_b5 hwf hm0 fun st5 hm5 hpc5 ↦ ?_
  have hpc5' : st5.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Climb.b6Offset) := by
    simp only [PcOk, SBool.eval, CmpOp.apply, Sym.eval, Sym.low_W64, hx22] at hpc5
    have hlt : (BitVec.ofNat 64 (4 * l)).ult (BitVec.ofNat 64 124) = decide (4 * l < 124) := by
      simp only [BitVec.ult, BitVec.toNat_ofNat]
      congr 1
      apply propext
      rw [Nat.mod_eq_of_lt (show 4 * l < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by decide)]
    have heq : (BitVec.ofNat 64 (4 * l) == BitVec.ofNat 64 124) = decide (4 * l = 124) := by
      by_cases h : 4 * l = 124
      · simp [h]
      · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
        intro he
        have := congrArg BitVec.toNat he
        simp at this
        omega
    rw [hpc5, hlt, heq]
    by_cases h : 4 * l < 124
    · simp [h, Nat.add_assoc, b5_next]
    · simp [show 4 * l = 124 by omega, Nat.add_assoc, b5_next]
  have hm5' : Match (env1 m0 l m) (after b5 headS) st5.data := by rw [after_eq run_b5]; exact hm5
  refine exec_at hk6 run_b6 hwf hpc5' hm5' fun st6 hm6 hpc6 ↦ ?_
  have hm6' : Match (env1 m0 l m) (after b6 (after b5 headS)) st6.data := by
    rw [after_eq run_b6]; exact hm6
  have hstep : (climbTo N m0.regs.X2 P (l + 1)).1 =
      (climbStep (climbTo N m0.regs.X2 P l) P[l]).1 := by rw [climbTo_succ _ _ _ hl]
  simp only [PcOk, SBool.eval, Sym.eval, hx21, getLsbD_low_zero] at hpc6
  by_cases hq : (climbTo N m0.regs.X2 P l).2 % 2 = 0
  · -- Even: `b2`, the accumulator left.
    simp only [hq, ne_eq, not_true_eq_false, decide_false, Bool.not_false, ↓reduceIte] at hpc6
    rw [hl2] at hpc6
    refine exec_at hk2 run_b2 hwf hpc6 hm6' fun st2 hm2 hpc2 ↦ ?_
    have hm2' : Match (env1 m0 l m) (after b2 (after b6 (after b5 headS))) st2.data := by
      rw [after_eq run_b2]; exact hm2
    refine exec_at hk3 run_b3l hwf hpc2 hm2' fun st3 hm3 hpc3 ↦ ?_
    refine after_call hhp hpre hinv false hm3 (by rw [after_eq run_b6]) rfl rfl rfl rfl
      (fun r hr ↦ by
        simp only [outer, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      ?_ hpc3
    rw [hstep, climbStep]
    simp [hq]
  · -- Odd: `b7`, `b9`, the accumulator right.
    simp only [hq, ne_eq, not_false_eq_true, decide_true, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte] at hpc6
    refine exec_at hk7 run_b7 hwf hpc6 hm6' fun st7 hm7 hpc7 ↦ ?_
    have hm7' : Match (env1 m0 l m) (after b7 (after b6 (after b5 headS))) st7.data := by
      rw [after_eq run_b7]; exact hm7
    rw [PcOk, hl7] at hpc7
    refine exec_at hk9 run_b9 hwf hpc7 hm7' fun st9 hm9 hpc9 ↦ ?_
    have hm9' : Match (env1 m0 l m) (after b9 (after b7 (after b6 (after b5 headS))))
        st9.data := by rw [after_eq run_b9]; exact hm9
    rw [PcOk, hl3] at hpc9
    refine exec_at hk3 run_b3r hwf hpc9 hm9' fun st3 hm3 hpc3 ↦ ?_
    refine after_call hhp hpre hinv true hm3 (by rw [after_eq run_b6]) rfl rfl rfl rfl
      (fun r hr ↦ by
        simp only [outer, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      ?_ hpc3
    rw [hstep, climbStep]
    simp [hq]

end

end NativeRustcVmArm.Sumcheck.Climb
