module

public import NativeRustcVmArm.Code.Vm.ReaderLe.Names
public import NativeRustcVmArm.Code.Vm.ReaderWords.Names
public import NativeRustcVmArm.Wire.ReaderWords.Exec
public import NativeRustcVmArm.Wire.Frame

/-!
# `Reader::words` meets its contract

`readerWords_spec`: the bound check (`b0`) fails: `None` (`b1`); else no word (`b2`) or the loop
(`b3`, then `b4`, `b5`, `b6` per word, `LInv`): each word read by `Reader::le`, which cannot fail
within the bound, and stored; then `Some` (`b7`, `finish`).
-/

namespace NativeRustcVmArm.Wire.ReaderWords

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.ReaderWords
open LeanVM.Parameters

@[expose] public section

/-- The prologue's slots. -/
def slots : List (Nat × XReg) := [(24, .X19), (16, .X20), (8, .X21), (0, .X30)]

/-- The callee-saved registers it does not save. -/
def keep : List XReg := [.X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29]

/-- The output's bytes. -/
abbrev W (m0 : MachineData) : BitVec 64 → Prop := InRange m0.regs.X1.toBitVec (8 * m0.regs.X2.toNat)

/-- The state between the prologue and the epilogue. -/
abbrev Frm (m0 m : MachineData) : Prop := Fr m0 32 32 slots keep (outs m0.regs.X0.toBitVec (W m0)) m

/-- The words read from `c`, the first `i`. -/
def wordsFrom (B : List UInt8) (c i : Nat) : List UInt64 := (List.range i).map fun j ↦ leAt B (c + 8 * j) 8

/-- What `Reader::words` reaches. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ ReaderWordsPost m0 st.data

/-- The environment of the frame. -/
abbrev frEnv (m0 m : MachineData) : Env := Env.ofMachine m [(base m0 32, 32)]

end

public section

theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit} (h : exec ds S = some (S₁, x)) :
    after ds S = S₁ := by
  rw [after, h]

theorem geo_of [Labels] {m0 : MachineData} (h : ReaderWordsPre m0) {bp : BitVec 64}
    {B : List UInt8} {c : Nat} (hR : ReaderAt m0.dmem m0.regs.X0.toBitVec bp B c) :
    RGeo m0 32 m0.regs.X0.toBitVec bp B.length (W m0) ∧
      NativeRustcVm.Mapped m0.dmem m0.regs.X1.toBitVec (8 * m0.regs.X2.toNat) ∧
      NoWrap m0.regs.X1.toBitVec (8 * m0.regs.X2.toNat) := by
  obtain ⟨hst, ⟨hom, honw⟩, bp', B', c', hR', hd⟩ := h
  obtain ⟨rfl, rfl, rfl⟩ := hR'.unique hR
  simp only [NativeRustcVm.Disjoint, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] at hd
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6, -⟩ := hd
  exact ⟨RGeo.of_apart hst hR.ok.2 hR.noWrap honw h1 h2 h3 h4 h5 h6, hom, honw⟩

theorem frEnv_wf {m0 m : MachineData} (hst : StackOk m0 32) (hfr : Frm m0 m) : (frEnv m0 m).WF :=
  Env.wf_of ⟨⟨fun i hi ↦ hfr.kept _ (hst.2.2 i hi), Ring.base_noWrap hst.2.1⟩, trivial⟩
    (List.pairwise_singleton _ _)

theorem base_aligned {m0 : MachineData} (hst : StackOk m0 32) : (base m0 32).toNat % 16 = 0 := by
  rw [Ring.base_toNat hst.2.1]; have := hst.1; omega

theorem frEnv_match [Labels] {m0 m : MachineData} (hst : StackOk m0 32) (hfr : Frm m0 m) :
    Match (frEnv m0 m) frS m :=
  match_ofMachine ⟨rfl, fun _ ↦ base_aligned hst, trivial⟩ (by rw [hfr.sp]; simp [Sym.eval])
    trivial trivial trivial trivial

/-- The postcondition from the reader's bytes and cursor, and the frame's changes. -/
theorem post_of [Labels] {m0 m : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}
    (hR : ReaderAt m0.dmem m0.regs.X0.toBitVec bp B c)
    (hres : match rdWords B m0.regs.X2.toNat c with
      | some (ws, c') => m.regs.X0 = 1 ∧ WordsAt m.dmem m0.regs.X1.toBitVec (ws.map K.lane) ∧
          ReaderAt m.dmem m0.regs.X0.toBitVec bp B c'
      | none => m.regs.X0 = 0)
    (hs : SameOutside m0.dmem m.dmem fun q ↦ InRange (base m0 32) 32 q ∨
      outs m0.regs.X0.toBitVec (W m0) q) (hsv : Saved m0 m) :
    ReaderWordsPost m0 m := by
  refine ⟨fun bp' B' c' hR' ↦ ?_, fun p hp ↦ hs p ?_, hsv⟩
  · obtain ⟨rfl, rfl, rfl⟩ := hR.unique hR'
    exact hres
  · rintro (h | h | h)
    · exact hp ⟨stackR m0 readerWordsStack, by simp, h⟩
    · exact hp ⟨curRegion m0.regs.X0.toBitVec, by simp, h⟩
    · exact hp ⟨_, List.mem_cons_self, h⟩

variable [Host] {k : Nat}

theorem lbl (hp : Placed code k) {j : Nat} {l : Label} (h : Vm.ReaderWords.code[j]? = some (.label l)) :
    Labels.label l = Host.addrOf (k + j) :=
  hp.label h

/-- **`None`** (`b1`), the bound check failed. -/
theorem fail (hp : Placed code k) {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}
    (hst : StackOk m0 32) (hR : ReaderAt m0.dmem m0.regs.X0.toBitVec bp B c)
    (hfit : ¬c + 8 * m0.regs.X2.toNat ≤ B.length) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ReaderWords.b1Offset)) (hfr : Frm m0 st.data) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hwf := frEnv_wf hst hfr
  have hm := frEnv_match hst hfr
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hret, hsv⟩ := hfr.exit hm1 hwf (by decide)
  have hd : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  refine .done _ ⟨by simp only [PcOk] at hpc1; rw [hpc1, hret], post_of hR ?_ ?_ hsv⟩
  · simp only [rdWords, hfit, ↓reduceIte]
    exact UInt64.toBitVec_inj.mp (hm1.regs .X0 _ rfl)
  · rw [hd]; exact hfr.same

/-- At `b7`: the words read, the reader past them. -/
structure Done (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c : Nat) (st : MachineState) :
    Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ReaderWords.b7Offset)
  fr : Frm m0 st.data
  fit : c + 8 * m0.regs.X2.toNat ≤ B.length
  rd : ReaderAt st.data.dmem m0.regs.X0.toBitVec bp B (c + 8 * m0.regs.X2.toNat)
  ws : WordsAt st.data.dmem m0.regs.X1.toBitVec (wordsFrom B c m0.regs.X2.toNat)

/-- **`Some`** (`b7`). -/
theorem finish (hp : Placed code k) {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}
    (hst : StackOk m0 32) (hR : ReaderAt m0.dmem m0.regs.X0.toBitVec bp B c) {st : MachineState}
    (hD : Done (k := k) m0 bp B c st) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hwf := frEnv_wf hst hD.fr
  have hm := frEnv_match hst hD.fr
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) run_b7 hwf hD.pc hm fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hret, hsv⟩ := hD.fr.exit hm1 hwf (by decide)
  have hd : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  refine .done _ ⟨by simp only [PcOk] at hpc1; rw [hpc1, hret], post_of hR ?_ ?_ hsv⟩
  · simp only [rdWords, hD.fit, ↓reduceIte]
    refine ⟨UInt64.toBitVec_inj.mp (hm1.regs .X0 _ rfl), ?_, by rw [hd]; exact hD.rd⟩
    rw [hd, List.map_map]
    exact hD.ws
  · rw [hd]; exact hD.fr.same

/-- The loop's head (`b4`) after `i` words. -/
structure LInv (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c i : Nat) (st : MachineState) :
    Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ReaderWords.b4Offset)
  fr : Frm m0 st.data
  lt : i < m0.regs.X2.toNat
  fit : c + 8 * m0.regs.X2.toNat ≤ B.length
  x19 : (st.data.regs.getXReg .X19).toBitVec = m0.regs.X0.toBitVec
  x20 : (st.data.regs.getXReg .X20).toBitVec = m0.regs.X1.toBitVec + BitVec.ofNat 64 (8 * i)
  x21 : (st.data.regs.getXReg .X21).toNat = 8 * (m0.regs.X2.toNat - i)
  rd : ReaderAt st.data.dmem m0.regs.X0.toBitVec bp B (c + 8 * i)
  ws : WordsAt st.data.dmem m0.regs.X1.toBitVec (wordsFrom B c i)

/-- The loop's environment: the frame and the next output word. -/
abbrev loopEnv (m0 m : MachineData) (i : Nat) : Env :=
  Env.ofMachine m [(base m0 32, 32), (m0.regs.X1.toBitVec + BitVec.ofNat 64 (8 * i), 8)]

section Loop

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c i : Nat}

omit [Host] in
theorem word_window (hst : StackOk m0 32) (g : RGeo m0 32 m0.regs.X0.toBitVec bp B.length (W m0))
    (hom : NativeRustcVm.Mapped m0.dmem m0.regs.X1.toBitVec (8 * m0.regs.X2.toNat))
    (honw : NoWrap m0.regs.X1.toBitVec (8 * m0.regs.X2.toNat)) (hi : i < m0.regs.X2.toNat)
    {m : MachineData} (hfr : Frm m0 m) : (loopEnv m0 m i).WF := by
  have hb := Ring.base_noWrap (m0 := m0) (F := 32) hst.2.1
  unfold NoWrap at honw
  have hto : (m0.regs.X1.toBitVec + BitVec.ofNat 64 (8 * i)).toNat = m0.regs.X1.toBitVec.toNat + 8 * i :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  refine Env.wf_of ⟨⟨fun j hj ↦ hfr.kept _ (hst.2.2 j hj), hb⟩, ⟨fun j hj ↦ ?_, ?_⟩, trivial⟩
    (List.pairwise_pair.mpr ?_)
  · rw [NativeRustcVm.addr_add_add]
    exact hfr.kept _ (hom _ (by omega))
  · show NativeRustcArm.NoWrap _ _
    unfold NativeRustcArm.NoWrap; rw [hto]; omega
  · show NativeRustcArm.Apart _ _ _ _
    have := g.wS (m0.regs.X1.toBitVec + BitVec.ofNat 64 (8 * i))
      (NativeRustcVm.inRange_add (by omega) (by omega))
    have h2 := g.wS (m0.regs.X1.toBitVec + BitVec.ofNat 64 (8 * i + 7))
      (NativeRustcVm.inRange_add (by omega) (by omega))
    rw [Sym.inRange_iff hb, Ring.base_toNat hst.2.1] at this h2
    rw [NativeRustcVm.toNat_add_ofNat (by omega)] at h2
    unfold NativeRustcArm.Apart
    rw [Ring.base_toNat hst.2.1, hto]
    omega

omit [Host] in
theorem keep_atoms : ∀ x ∈ keep, loopS.reg x = some (.reg x) := by decide

omit [Host] in
theorem keep_saved : ∀ x ∈ keep, calleeSaved x = true := by decide

omit [Host] in
theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 32 := by decide

omit [Host] in
theorem loopEnv_match [Labels] (hst : StackOk m0 32) {m : MachineData} (hfr : Frm m0 m)
    (h20 : (m.regs.getXReg .X20).toBitVec = m0.regs.X1.toBitVec + BitVec.ofNat 64 (8 * i)) :
    Match (loopEnv m0 m i) loopS m :=
  match_ofMachine ⟨rfl, fun _ ↦ base_aligned hst, rfl, nofun, trivial⟩
    (by rw [hfr.sp]; simp [Sym.eval])
    ⟨show (m.regs.getXReg .X20).toBitVec = _ by rw [h20]; simp [Sym.eval], trivial⟩ trivial trivial trivial

/-- **One word**: from the loop's head after `i` words, the next read and stored; back at the head
or done. -/
theorem step (hp : Placed code k) (hle : Spec (Labels.label NativeRustcVmArm.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost)
    (hst : StackOk m0 32) (g : RGeo m0 32 m0.regs.X0.toBitVec bp B.length (W m0))
    (hom : NativeRustcVm.Mapped m0.dmem m0.regs.X1.toBitVec (8 * m0.regs.X2.toNat))
    (honw : NoWrap m0.regs.X1.toBitVec (8 * m0.regs.X2.toNat)) {st : MachineState}
    (hI : LInv (k := k) m0 bp B c i st) :
    Eventually (step1 Host.exe)
      (fun st' ↦ Done (k := k) m0 bp B c st' ∨ LInv (k := k) m0 bp B c (i + 1) st') st := by
  have hn := hI.lt
  have hwf := word_window hst g hom honw hn hI.fr
  have hm := loopEnv_match hst hI.fr hI.x20
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf hI.pc hm fun st1 hm1 hpc1 ↦ ?_
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hfr1 : Frm m0 st1.data := Fr.ofBlock hI.fr hm hm1 hwf rfl rfl rfl fun x hx ↦
    ⟨.reg x, keep_atoms x hx, by revert x; decide⟩
  have hx0 : st1.data.regs.X0.toBitVec = m0.regs.X0.toBitVec := (hm1.regs .X0 _ rfl).trans hI.x19
  have hx1 : st1.data.regs.X1.toNat = 8 := by
    show (st1.data.regs.getXReg .X1).toBitVec.toNat = 8
    rw [hm1.regs .X1 (.lit 8) rfl]; rfl
  refine le_call hle g (by decide) (by omega) keep_saved slots_le hfr1 (by rw [hd1]; exact hI.rd)
    hx0 hx1 hpc1 fun m2 hfr2 hcs2 hs2 hres2 ↦ ?_
  rcases readRes_cases hres2 with ⟨_, hf⟩ | ⟨h21, hv, hR2, -⟩
  · exfalso; have := hI.fit; omega
  have h20 : (m2.regs.getXReg .X20).toBitVec = m0.regs.X1.toBitVec + BitVec.ofNat 64 (8 * i) := by
    rw [hcs2 .X20 rfl, Match.reg_eq hm hm1 rfl rfl]; exact hI.x20
  have h21' : (m2.regs.getXReg .X21).toNat = 8 * (m0.regs.X2.toNat - i) := by
    rw [hcs2 .X21 rfl, Match.reg_eq hm hm1 rfl rfl]; exact hI.x21
  have h19 : (m2.regs.getXReg .X19).toBitVec = m0.regs.X0.toBitVec := by
    rw [hcs2 .X19 rfl, Match.reg_eq hm hm1 rfl rfl]; exact hI.x19
  have hwf2 := word_window hst g hom honw hn hfr2
  have hm2 := loopEnv_match hst hfr2 h20
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 hwf2
    (by rw [Nat.add_assoc, b4_next]) hm2 fun st5 hm5 hpc5 ↦ ?_
  have hc5 : (SBool.not (SBool.cmp .eq .W64 (.reg .X0) (.lit 1))).eval (loopEnv m0 m2 i) = false := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, Sym.low_W64, Env.ofMachine_regs,
      show m2.regs.getXReg .X0 = m2.regs.X0 from rfl, h21]
    decide
  simp only [PcOk, hc5, Bool.false_eq_true, ↓reduceIte, NativeRustcVmArm.Vm.ReaderWords.b5_length, NativeRustcVmArm.Vm.ReaderWords.b5Length] at hpc5
  have r6 := run_b6
  rw [after_eq run_b5] at r6
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) r6 hwf2 hpc5 hm5 fun st6 hm6 hpc6 ↦ ?_
  rw [← after_eq r6] at hm6
  -- the frame
  have hnw := honw
  unfold NoWrap at hnw
  have hs6 : SameOutside m2.dmem st6.data.dmem
      (InRange (m0.regs.X1.toBitVec + BitVec.ofNat 64 (8 * i)) 8) := by
    have := Match.sameOutside_in hm6 hwf2 (r0 := 1) (o := 0) (n := 8) rfl (by omega)
      (by rw [after_eq r6]; decide)
    rwa [NativeRustcVm.addr_add_zero] at this
  have hWi : ∀ q, InRange (m0.regs.X1.toBitVec + BitVec.ofNat 64 (8 * i)) 8 q → W m0 q :=
    fun q hq ↦ NativeRustcVm.InRange.of_sub hq honw (by omega)
  have hfr6 : Frm m0 st6.data := by
    refine hfr2.step (Match.sp_eq hm2 hm6 (by rw [after_eq r6]; rfl)) (fun x hx ↦ ?_) (hm6.kept hwf2)
      hs6 (fun q hq ↦ .inr (.inr (hWi q hq))) fun p hp j hj hq ↦ ?_
    · exact Match.reg_eq hm2 hm6 (keep_atoms x hx) (by rw [after_eq r6]; revert x; decide)
    · have hsl := slots_le p hp
      refine g.wS _ (hWi _ hq) ?_
      rw [NativeRustcVm.addr_add_add]
      exact NativeRustcVm.inRange_add (by omega) (by have := Ring.base_noWrap (m0 := m0) (F := 32) hst.2.1; unfold NoWrap at this; omega)
  -- the reader, the words
  have hR6 : ReaderAt st6.data.dmem m0.regs.X0.toBitVec bp B (c + 8 * (i + 1)) :=
    g.reader_frame rfl hR2 (NativeRustcVm.SameOutside.mono hs6 fun q hq ↦ .inr (hWi q hq))
  have hlen : (wordsFrom B c i).length = i := by simp [wordsFrom]
  have hold : WordsAt st6.data.dmem m0.regs.X1.toBitVec (wordsFrom B c i) := by
    have h := hI.ws
    rw [← hd1] at h
    refine (h.of_sameOutside hs2 fun j hj hq ↦ ?_).of_sameOutside hs6 fun j hj hq ↦ ?_
    · rw [NativeRustcVm.length_wordsBytes, hlen] at hj
      have hW : W m0 (m0.regs.X1.toBitVec + BitVec.ofNat 64 j) :=
        NativeRustcVm.inRange_add (by omega) (by omega)
      refine g.wR _ hW ?_
      exact NativeRustcVm.InRange.of_sub (o := 16) (m := 8) hq g.rNw (by omega)
    · rw [NativeRustcVm.length_wordsBytes, hlen] at hj
      exact NativeRustcVm.not_inRange_sub honw (by omega) (by omega) (.inl hj) hq
  have hnew : WordAt st6.data.dmem (m0.regs.X1.toBitVec + BitVec.ofNat 64 (8 * i)) (leAt B (c + 8 * i) 8) := by
    have h := hm6.bytesAt_write (r := 1) (o := 0) (n := 8)
      (b := m0.regs.X1.toBitVec + BitVec.ofNat 64 (8 * i)) (sz := 8) rfl (by omega) (v := .reg .X1)
      (by rw [after_eq r6]; decide)
    rw [byteOf_range, NativeRustcVm.addr_add_zero] at h
    rw [← hv]
    exact h
  have hws : WordsAt st6.data.dmem m0.regs.X1.toBitVec (wordsFrom B c (i + 1)) := by
    rw [show wordsFrom B c (i + 1) = wordsFrom B c i ++ [leAt B (c + 8 * i) 8] by
      simp [wordsFrom, List.range_succ], NativeRustcVm.wordsAt_append_iff,
      show (wordsFrom B c i).length = i by simp [wordsFrom], NativeRustcVm.wordsAt_singleton_iff]
    exact ⟨hold, hnew⟩
  -- the registers
  have e6 : ∀ x v, (after b6 (after b5 loopS)).reg x = some v →
      (st6.data.regs.getXReg x).toBitVec = v.eval (loopEnv m0 m2 i) := fun x v h ↦ by
    rw [after_eq run_b5] at h; exact hm6.regs x v h
  have h19' : (st6.data.regs.getXReg .X19).toBitVec = m0.regs.X0.toBitVec := by
    rw [e6 .X19 (.reg .X19) (by decide)]; exact h19
  have h20' : (st6.data.regs.getXReg .X20).toBitVec =
      m0.regs.X1.toBitVec + BitVec.ofNat 64 (8 * (i + 1)) := by
    rw [e6 .X20 (.ptr 1 8) (by decide)]
    simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.map_some, Option.getD_some]
    rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add,
      Nat.mul_succ]
  have hX21 : (m2.regs.getXReg .X21).toBitVec.toNat = 8 * (m0.regs.X2.toNat - i) := h21'
  have h21'' : (st6.data.regs.getXReg .X21).toNat = 8 * (m0.regs.X2.toNat - (i + 1)) := by
    show (st6.data.regs.getXReg .X21).toBitVec.toNat = _
    rw [e6 .X21 (.bin .sub .W64 (.reg .X21) (.lit 8)) (by decide)]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [BitVec.toNat_sub, hX21]
    simp only [BitVec.toNat_ofNat]
    omega
  have hc6 : (SBool.not (SBool.cmp .eq .W64 (.reg .X21) (.lit 8))).eval (loopEnv m0 m2 i) =
      decide (i + 1 < m0.regs.X2.toNat) := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, Sym.low_W64, Env.ofMachine_regs]
    by_cases h : i + 1 < m0.regs.X2.toNat
    · rw [decide_eq_true h]
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
      intro he
      have := congrArg BitVec.toNat he
      rw [hX21] at this
      simp at this
      omega
    · rw [decide_eq_false h]
      simp only [Bool.not_eq_false', beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [hX21]
      simp
      omega
  simp only [PcOk, NativeRustcVmArm.Vm.ReaderWords.b6_length, NativeRustcVmArm.Vm.ReaderWords.b6Length, hc6] at hpc6
  by_cases hlt : i + 1 < m0.regs.X2.toNat
  · simp only [decide_eq_true hlt, ↓reduceIte, lbl hp (j := 19) rfl] at hpc6
    exact .done _ (.inr ⟨hpc6, hfr6, hlt, hI.fit, h19', h20', h21'', hR6, hws⟩)
  · simp only [decide_eq_false hlt, Bool.false_eq_true, ↓reduceIte] at hpc6
    have he : m0.regs.X2.toNat = i + 1 := by omega
    exact .done _ (.inl ⟨hpc6.trans (congrArg Host.addrOf (by simpa only [b6_length, b6Length, Nat.add_assoc] using congrArg (k + ·) b6_next)), hfr6, hI.fit,
      by rw [he]; exact hR6, by rw [he]; exact hws⟩)

end Loop

omit [Host] in
/-- `lsl x, #3` (`ubfm x, #61, #60`) without overflow. -/
theorem ubfm_lsl3 {x : BitVec 64} (h : 8 * x.toNat < 2 ^ 64) :
    (UnOp.apply (.ubfm 61 60) .W64 x).toNat = 8 * x.toNat := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64]
  simp [evalUBFM, toNat_take', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- **`Reader::words` meets its contract.** -/
theorem readerWords_spec (hp : Placed code k)
    (hle : Spec (Labels.label NativeRustcVmArm.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost) :
    Spec (Labels.label NativeRustcVmArm.Vm.ReaderWords.entryLabel) ReaderWordsPre ReaderWordsPost := by
  intro m0 hpre
  obtain ⟨hst, -, bp, B, c, hR, -⟩ := id hpre
  replace hst : StackOk m0 32 := hst
  obtain ⟨g, hom, honw⟩ := geo_of hpre hR
  rw [lbl hp (j := 0) (l := NativeRustcVmArm.Vm.ReaderWords.entryLabel) rfl]
  have hnw := honw
  unfold NoWrap at hnw
  have hn64 : 8 * m0.regs.X2.toNat < 2 ^ 64 := by
    by_contra hc
    have hW : W m0 (base m0 32) := by
      show InRange _ _ _
      rw [Sym.inRange_iff honw, Ring.base_toNat hst.2.1]
      have := (base m0 32).isLt
      rw [Ring.base_toNat hst.2.1] at this
      omega
    exact g.wS _ hW (NativeRustcVm.inRange_self (by omega))
  let env0 := Env.ofMachine m0 [(base m0 32, 32), (m0.regs.X0.toBitVec, 24)]
  have hb := Ring.base_noWrap (m0 := m0) (F := 32) hst.2.1
  have hwf0 : env0.WF := Env.wf_of ⟨⟨hst.2.2, hb⟩, hR.ok, trivial⟩ (List.pairwise_pair.mpr g.sr)
  have hm0 : Match env0 entryS m0 := match_ofMachine ⟨rfl, fun _ ↦ base_aligned hst, rfl, nofun, trivial⟩
    (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]
        rw [show BitVec.ofInt 64 32 = BitVec.ofNat 64 32 from rfl]
        exact Ring.base_add_eq.symm)
    ⟨by simp [Sym.eval]; rfl, trivial⟩ trivial trivial trivial
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 hm0 fun s1 hm1 hpc1 ↦ ?_
  rw [← after_eq run_b0] at hm1
  have hfr1 : Frm m0 s1.data :=
    Fr.ofPrologue hst.2.1 (Nat.le_refl _) hm1 hwf0 (by decide) (by decide +kernel) (by decide)
      (by decide +kernel) (by decide)
  have hs1 := Match.sameOutside_in hm1 hwf0 (r0 := 0) (o := 0) (n := 32) rfl (by omega)
    (by decide +kernel)
  rw [NativeRustcVm.addr_add_zero] at hs1
  have hR1 : ReaderAt s1.data.dmem m0.regs.X0.toBitVec bp B c :=
    g.reader_frame rfl hR (NativeRustcVm.SameOutside.mono hs1 fun _ h ↦ .inl h)
  have hb1 : env0.base 1 = m0.regs.X0.toBitVec := Env.base_ofMachine m0 _ _ rfl
  have hL := hR.len_lt
  have hlen : env0.load 1 8 8 = B.length.toUInt64.toBitVec := load_word (by rw [hb1]; exact hR.len)
  have hcur : env0.load 1 16 8 = c.toUInt64.toBitVec := load_word (by rw [hb1]; exact hR.cur)
  have hc64 : c < 2 ^ 64 := by have := hR.c_le; omega
  have hn64' : 8 * (env0.regs .X2).toNat < 2 ^ 64 := hn64
  simp only [PcOk, ReaderLe.fits_eval, Sym.eval, hlen, hcur,
    ReaderLe.toBitVec_toUInt64_toNat hL, ReaderLe.toBitVec_toUInt64_toNat hc64,
    ubfm_lsl3 hn64', NativeRustcVmArm.Vm.ReaderWords.b0_length, NativeRustcVmArm.Vm.ReaderWords.b0Length] at hpc1
  have hx2 : (env0.regs .X2).toNat = m0.regs.X2.toNat := rfl
  rw [hx2] at hpc1
  by_cases hfit : c + 8 * m0.regs.X2.toNat ≤ B.length
  swap
  · simp only [decide_eq_false hfit, Bool.false_eq_true, ↓reduceIte] at hpc1
    exact fail hp hst hR hfit (hpc1.trans (congrArg Host.addrOf (by simpa only [b0_length, b0Length, b0Offset, Nat.add_zero, Nat.zero_add, Nat.add_assoc] using congrArg (k + ·) b0_next))) hfr1
  simp only [decide_eq_true hfit, ↓reduceIte, lbl hp (j := 15) rfl] at hpc1
  have e1 : ∀ x v, (after b0 entryS).reg x = some v →
      (s1.data.regs.getXReg x).toBitVec = v.eval env0 := fun x v h ↦ hm1.regs x v h
  have h0 : (s1.data.regs.getXReg .X0).toBitVec = m0.regs.X0.toBitVec := by
    rw [e1 .X0 (.ptr 1 0) (by decide)]; simp [Sym.eval, hb1]
  have h1 : (s1.data.regs.getXReg .X1).toBitVec = m0.regs.X1.toBitVec := e1 .X1 (.reg .X1) (by decide)
  have h2 : (s1.data.regs.getXReg .X2).toBitVec = m0.regs.X2.toBitVec := e1 .X2 (.reg .X2) (by decide)
  have h21 : (s1.data.regs.getXReg .X21).toNat = 8 * m0.regs.X2.toNat := by
    show (s1.data.regs.getXReg .X21).toBitVec.toNat = _
    rw [e1 .X21 (.un (.ubfm 61 60) .W64 (.reg .X2)) (by decide)]
    exact ubfm_lsl3 hn64'
  -- `b2`: no word?
  have hwf2 := frEnv_wf hst hfr1
  have hm2 := frEnv_match hst hfr1
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf2 hpc1 hm2 fun s2 hm2' hpc2 ↦ ?_
  have hd2 : s2.data.dmem = s1.data.dmem := hm2'.dmem_eq hwf2 rfl
  have hfr2 : Frm m0 s2.data := Fr.ofBlock hfr1 hm2 hm2' hwf2 rfl rfl rfl fun x hx ↦
    ⟨.reg x, by revert x; decide, by revert x; decide⟩
  have r2 : ∀ x : XReg, s2.data.regs.getXReg x = s1.data.regs.getXReg x := fun x ↦
    Match.reg_eq hm2 hm2' (v := .reg x) (by cases x <;> rfl) (by cases x <;> rfl)
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, Sym.low_W64, Env.ofMachine_regs, h2,
    NativeRustcVmArm.Vm.ReaderWords.b2_length, NativeRustcVmArm.Vm.ReaderWords.b2Length] at hpc2
  by_cases hn0 : m0.regs.X2.toNat = 0
  · have : (m0.regs.X2.toBitVec == BitVec.ofNat 64 0) = true := by
      simp only [beq_iff_eq]; apply BitVec.eq_of_toNat_eq; simp [hn0]
    simp only [this, ↓reduceIte, lbl hp (j := 28) rfl] at hpc2
    refine finish hp hst hR ⟨hpc2, hfr2, hfit, ?_, ?_⟩
    · rw [hn0, Nat.mul_zero, Nat.add_zero, hd2]; exact hR1
    · rw [hn0]; exact NativeRustcVm.wordsAt_nil _ _
  have : (m0.regs.X2.toBitVec == BitVec.ofNat 64 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro he
    exact hn0 (by have := congrArg BitVec.toNat he; simpa using this)
  simp only [this, Bool.false_eq_true, ↓reduceIte] at hpc2
  -- `b3`: the loop's set-up
  have hwf3 := frEnv_wf hst hfr2
  have hm3 := frEnv_match hst hfr2
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf3 hpc2 hm3 fun s3 hm3' hpc3 ↦ ?_
  have hd3 : s3.data.dmem = s2.data.dmem := hm3'.dmem_eq hwf3 rfl
  have hfr3 : Frm m0 s3.data := Fr.ofBlock hfr2 hm3 hm3' hwf3 rfl rfl rfl fun x hx ↦
    ⟨.reg x, by revert x; decide, by revert x; decide⟩
  have e3 : ∀ x v, (after b3 frS).reg x = some v →
      (s3.data.regs.getXReg x).toBitVec = v.eval (frEnv m0 s2.data) := fun x v h ↦ by
    rw [after_eq run_b3] at h; exact hm3'.regs x v h
  simp only [PcOk, NativeRustcVmArm.Vm.ReaderWords.b3_length, NativeRustcVmArm.Vm.ReaderWords.b3Length] at hpc3
  have hI0 : LInv (k := k) m0 bp B c 0 s3 := by
    refine ⟨hpc3, hfr3, by omega, hfit, ?_, ?_, ?_, ?_, NativeRustcVm.wordsAt_nil _ _⟩
    · rw [e3 .X19 (.reg .X0) (by decide)]
      show (s2.data.regs.getXReg .X0).toBitVec = _
      rw [r2]; exact h0
    · rw [e3 .X20 (.reg .X1) (by decide)]
      show (s2.data.regs.getXReg .X1).toBitVec = _
      rw [r2, h1]; simp
    · show (s3.data.regs.getXReg .X21).toBitVec.toNat = _
      rw [e3 .X21 (.reg .X21) (by decide)]
      show (s2.data.regs.getXReg .X21).toBitVec.toNat = _
      rw [r2]; exact h21
    · rw [Nat.mul_zero, Nat.add_zero, hd3, hd2]; exact hR1
  refine Sym.loop (fun n st ↦ ∃ i, n = m0.regs.X2.toNat - i ∧ LInv (k := k) m0 bp B c i st)
    (fun n st ⟨i, hn, hI⟩ ↦ ?_) ⟨0, rfl, hI0⟩
  refine Eventually.bind (step hp hle hst g hom honw hI) fun st' h ↦ ?_
  rcases h with hD | hI'
  · exact Eventually.mono (finish hp hst hR hD) fun _ h ↦ .inl h
  · exact .done _ (.inr ⟨_, by have := hI.lt; omega, i + 1, rfl, hI'⟩)

end

end NativeRustcVmArm.Wire.ReaderWords
