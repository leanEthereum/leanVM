module

public import NativeRustcVmX64.Wire.ReaderWords.Exec
public import NativeRustcVmX64.Wire.Frame
public import NativeRustcVmX64.Transcript.Arith
public import NativeRustcVmX64.Code.Vm.ReaderLe.Names

/-!
# `Reader::words`' loop (x86-64)

The places (`geo`), what a run changes of the entry's memory (`Chg`: the frame, the reader's
cursor, the output), a block from `frS` (`fr_step`), the epilogue (`fin`), and the loop: at its
head after `i` words (`LInv`), the next word read by `Reader::le` (which cannot fail within the
bound) and stored (`step`), back at the head or done (`Done`).
-/

namespace NativeRustcVmX64.Wire.ReaderWords

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.ReaderWords
open NativeRustcVmX64.Transcript (Frame frameEnv frame_wf frame_mapped frame_noWrap
  Frame.of_block Frame.epilogue Frame.load_ret sameOutside_low sameOutside_region wordAt_write
  after after_eq known_ptr inRange_mono MidOk EpiOk low8_replaceLow)
open NativeRustcVm.Transcript (Mapped.keeps off_zero off_off)
open LeanVM.Parameters

@[expose] public section

/-- The words read from `c`, the first `i`. -/
def wordsFrom (B : List UInt8) (c i : Nat) : List UInt64 :=
  (List.range i).map fun j ↦ leAt B (c + 8 * j) 8

/-- What a run may change of the entry's memory: the frame, the reader's cursor, the output. -/
def Chg (m0 d : MachineData) : Prop :=
  NativeRustcVm.SameOutside m0.dmem d.dmem fun q ↦
    NativeRustcVm.InRange (stackBelow m0 48) 48 q ∨
      NativeRustcVm.InRange (reg m0 .rdi + BitVec.ofNat 64 16) 8 q ∨
      NativeRustcVm.InRange (reg m0 .rsi) (8 * (reg m0 .rdx).toNat) q

/-- What `Reader::words` reaches. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ ReaderWordsPost m0 st.data

/-- The places of `Reader::words`. -/
structure Geo (m0 : MachineData) (bp : BitVec 64) (L : Nat) : Prop where
  g : RGeo m0 48 (reg m0 .rdi) bp L (NativeRustcVm.InRange (reg m0 .rsi) (8 * (reg m0 .rdx).toNat))
  om : NativeRustcVm.Mapped m0.dmem (reg m0 .rsi) (8 * (reg m0 .rdx).toNat)
  onw : NativeRustcVm.NoWrap (reg m0 .rsi) (8 * (reg m0 .rdx).toNat)
  oS : NativeRustcVm.Apart (reg m0 .rsi) (8 * (reg m0 .rdx).toNat) (stackBelow m0 48) (48 + 8)

end

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 48 := by decide

theorem stack_eq : readerWordsStack = 48 := rfl

theorem wordsFrom_succ (B : List UInt8) (c i : Nat) :
    wordsFrom B c (i + 1) = wordsFrom B c i ++ [leAt B (c + 8 * i) 8] := by
  simp [wordsFrom, List.range_succ]

theorem length_wordsFrom (B : List UInt8) (c i : Nat) : (wordsFrom B c i).length = i := by
  simp [wordsFrom]

/-- `AL` after `movb $1, %al`. -/
theorem merge_one (x : BitVec 64) :
    (BinOp.apply .merge .W8 x (BitVec.ofNat 64 1)).toNat % 256 = 1 := by
  have h := congrArg BitVec.toNat (low8_replaceLow x (low .W8 (BitVec.ofNat 64 1)))
  simp only [low, BitVec.toNat_setWidth] at h
  simp only [BinOp.apply, low]
  exact h

theorem geo_of {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}
    (hst : StackOk m0 readerWordsStack)
    (hout : NativeRustcVm.Region.Ok m0.dmem ⟨reg m0 .rsi, 8 * (reg m0 .rdx).toNat⟩)
    (hR : ReaderAt m0.dmem (reg m0 .rdi) bp B c)
    (hd : NativeRustcVm.Disjoint [stackR m0 readerWordsStack, ⟨reg m0 .rdi, 24⟩,
      ⟨bp, B.length⟩, ⟨reg m0 .rsi, 8 * (reg m0 .rdx).toNat⟩]) : Geo m0 bp B.length := by
  simp only [NativeRustcVm.Disjoint, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, stackR, stack_eq] at hd
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6, -⟩ := hd
  have hS := NativeRustcVmX64.noWrap_stackBelow hst
  have hoS : NativeRustcVm.Apart (reg m0 .rsi) (8 * (reg m0 .rdx).toNat) (stackBelow m0 48)
      (48 + 8) := by unfold NativeRustcVm.Apart at h3 ⊢; omega
  refine ⟨⟨hst, hR.ok.2, hR.noWrap, by unfold NativeRustcVm.Apart at h1 ⊢; omega,
    by unfold NativeRustcVm.Apart at h2 ⊢; omega, h4, fun q hq ↦ ?_, fun q hq ↦ ?_,
    fun q hq ↦ ?_⟩, hout.1, hout.2, hoS⟩
  · exact hoS.not_inRange hout.2 hS hq
  · exact (show NativeRustcVm.Apart (reg m0 .rsi) (8 * (reg m0 .rdx).toNat) (reg m0 .rdi) 24 by
      unfold NativeRustcVm.Apart at h5 ⊢; omega).not_inRange hout.2 hR.ok.2 hq
  · exact (show NativeRustcVm.Apart (reg m0 .rsi) (8 * (reg m0 .rdx).toNat) bp B.length by
      unfold NativeRustcVm.Apart at h6 ⊢; omega).not_inRange hout.2 hR.noWrap hq

theorem chg_trans {m0 d d' : MachineData} (h : Chg m0 d) {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem R)
    (hR : ∀ q, R q → NativeRustcVm.InRange (stackBelow m0 48) 48 q ∨
      NativeRustcVm.InRange (reg m0 .rdi + BitVec.ofNat 64 16) 8 q ∨
      NativeRustcVm.InRange (reg m0 .rsi) (8 * (reg m0 .rdx).toNat) q) : Chg m0 d' :=
  fun q hq ↦ (hs q fun h ↦ hq (hR q h)).trans (h q hq)

/-- The reader survives a change the run allows. -/
theorem Geo.reader {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}
    (g : Geo m0 bp B.length) {d d' : DataMem} (hR : ReaderAt d (reg m0 .rdi) bp B c)
    (hs : NativeRustcVm.SameOutside d d' fun q ↦ NativeRustcVm.InRange (stackBelow m0 48) 48 q ∨
      NativeRustcVm.InRange (reg m0 .rsi) (8 * (reg m0 .rdx).toNat) q) :
    ReaderAt d' (reg m0 .rdi) bp B c :=
  g.g.reader_frame rfl hR fun q hq ↦ hs q fun h ↦ hq (h.imp_left fun h ↦ inRange_mono h (by omega))

/-- The postcondition from the reader's own bytes and cursor. -/
theorem post_of {m0 m : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}
    (hR : ReaderAt m0.dmem (reg m0 .rdi) bp B c)
    (hres : match rdWords B (reg m0 .rdx).toNat c with
      | some (ws, c') => boolRet m = 1 ∧
          NativeRustcVm.WordsAt m.dmem (reg m0 .rsi) (ws.map K.lane) ∧
          ReaderAt m.dmem (reg m0 .rdi) bp B c'
      | none => boolRet m = 0)
    (hchg : Chg m0 m) (hsv : Saved m0 m) : ReaderWordsPost m0 m := by
  refine ⟨fun bp' B' c' hR' ↦ ?_, fun q hq ↦ hchg q ?_, hsv⟩
  · obtain ⟨rfl, rfl, rfl⟩ := hR.unique hR'
    exact hres
  · rintro (h | h | h)
    · exact hq ⟨frameR m0 readerWordsStack, by simp, h⟩
    · exact hq ⟨curRegion (reg m0 .rdi), by simp, h⟩
    · exact hq ⟨_, List.mem_cons_self, h⟩

variable [Host] {k : Nat}

/-- **A block from `frS`** (at `j`): memory and the frame kept. -/
theorem fr_step (hp : Placed code k) {m0 : MachineData} (hst : StackOk m0 48) {bj : List Directive}
    {j : Nat} (hb : bj.IsInfixAt code j) (hne : bj ≠ []) {x : Exit}
    (hrun : exec bj frS = some (after bj frS, x)) (hx : ∀ l, x = .call l → False)
    (hok : FrOk (after bj frS) = true)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + j)) (hf : Frame m0 48 slots 8 st.data)
    {R : MachineState → Prop}
    (cont : ∀ st', Frame m0 48 slots 8 st'.data → st'.data.dmem = st.data.dmem →
      Match (frameEnv m0 st.data 48 []) (after bj frS) st'.data →
      PcOk (frameEnv m0 st.data 48 []) x (Host.addrOf (k + j + bj.length)) st' →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  simp only [FrOk, Bool.and_eq_true, List.isEmpty_iff] at hok
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 48) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.kept, frame_noWrap hst (by decide)⟩
    (by simp) (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 st.data 48 []) frS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial trivial
  exact exec_at (infix_of hb hne hp) hrun hwf (fun l h ↦ (hx l h).elim) hpc hm fun st' hm' hpc' ↦
    cont st' (Frame.of_block hf hwf hm' hok.1 slots_le) (hm'.dmem_eq hwf hok.2) hm' hpc'

/-- **The epilogue** (`b9`, at `NativeRustcVmX64.Vm.ReaderWords.label_8`): RAX and memory as they are. -/
theorem fin (hp : Placed code k) {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}
    (hst : StackOk m0 48) (hR : ReaderAt m0.dmem (reg m0 .rdi) bp B c) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ReaderWords.b9Offset)) (hf : Frame m0 48 slots 8 st.data)
    (hres : match rdWords B (reg m0 .rdx).toNat c with
      | some (ws, c') => boolRet st.data = 1 ∧
          NativeRustcVm.WordsAt st.data.dmem (reg m0 .rsi) (ws.map K.lane) ∧
          ReaderAt st.data.dmem (reg m0 .rdi) bp B c'
      | none => boolRet st.data = 0)
    (hchg : Chg m0 st.data) : Eventually (step1 Host.exe) (Post m0) st := by
  obtain ⟨hepi, hmem, hrax⟩ := ok_b9
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 48) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.kept, frame_noWrap hst (by decide)⟩
    (by simp) (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 st.data 48 []) frS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) exit_b9 hwf nofun hpc hm
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hf hwf hm' hepi
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf hmem
  have ha : reg st'.data .rax = reg st.data .rax := hm'.regs .rax _ hrax
  simp only [PcOk] at hpc'
  refine .done _ ⟨by rw [hpc']; exact hf.load_ret hst (by decide), hrsp, post_of hR ?_
    (fun q hq ↦ by rw [hd]; exact hchg q hq) hsv⟩
  unfold boolRet
  rw [ha, hd]
  exact hres

/-- The loop's head (`b4`) after `i` words. -/
structure LInv (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c i : Nat)
    (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ReaderWords.b4Offset)
  fr : Frame m0 48 slots 8 st.data
  lt : i < (reg m0 .rdx).toNat
  fit : c + 8 * (reg m0 .rdx).toNat ≤ B.length
  r14 : reg st.data .r14 = reg m0 .rdi
  rbx : reg st.data .rbx = reg m0 .rsi
  r12 : reg st.data .r12 = BitVec.ofNat 64 (8 * i)
  r15 : reg st.data .r15 = BitVec.ofNat 64 (8 * (reg m0 .rdx).toNat)
  rd : ReaderAt st.data.dmem (reg m0 .rdi) bp B (c + 8 * i)
  ws : NativeRustcVm.WordsAt st.data.dmem (reg m0 .rsi) (wordsFrom B c i)
  chg : Chg m0 st.data

/-- After the loop (`b7`). -/
structure Done (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c : Nat)
    (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ReaderWords.b7Offset)
  fr : Frame m0 48 slots 8 st.data
  fit : c + 8 * (reg m0 .rdx).toNat ≤ B.length
  rd : ReaderAt st.data.dmem (reg m0 .rdi) bp B (c + 8 * (reg m0 .rdx).toNat)
  ws : NativeRustcVm.WordsAt st.data.dmem (reg m0 .rsi) (wordsFrom B c (reg m0 .rdx).toNat)
  chg : Chg m0 st.data

/-- The loop's environment: the frame and output word `i`. -/
abbrev loopEnv (m0 m : MachineData) (i : Nat) (ret : BitVec 64) : Env :=
  frameEnv m0 m 48 [(reg m0 .rsi + BitVec.ofNat 64 (8 * i), 8)] (fun _ ↦ 0) ret

section Loop

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c i : Nat}

omit [Host] in
theorem window (g : Geo m0 bp B.length) (hi : i < (reg m0 .rdx).toNat) :
    (reg m0 .rsi + BitVec.ofNat 64 (8 * i)).toNat = (reg m0 .rsi).toNat + 8 * i := by
  have := g.onw
  unfold NativeRustcVm.NoWrap at this
  exact NativeRustcVm.toNat_add_ofNat (by omega)

omit [Host] in
theorem loop_wf (g : Geo m0 bp B.length) (hi : i < (reg m0 .rdx).toNat) {m : MachineData}
    (hf : Frame m0 48 slots 8 m) {ret : BitVec 64} : (loopEnv m0 m i ret).WF := by
  have hw := window g hi
  have honw := g.onw
  have hoS := g.oS
  unfold NativeRustcVm.NoWrap at honw
  refine frame_wf ⟨Mapped.keeps (frame_mapped g.g.st (by decide)) hf.kept,
    frame_noWrap g.g.st (by decide)⟩ (fun x hx ↦ ?_) (List.pairwise_pair.mpr ?_)
  · rw [List.mem_singleton] at hx
    subst hx
    refine ⟨fun j hj ↦ ?_, ?_⟩
    · rw [NativeRustcVm.addr_add_add]
      exact hf.kept _ (g.om _ (by dsimp only at hj; omega))
    · show _ + 8 ≤ 2 ^ 64
      rw [hw]; omega
  · unfold NativeRustcVm.Apart at hoS ⊢
    dsimp only
    rw [hw]
    omega

theorem loop_match {m : MachineData} (hf : Frame m0 48 slots 8 m)
    (hrbx : reg m .rbx = reg m0 .rsi) (hr12 : reg m .r12 = BitVec.ofNat 64 (8 * i))
    {ret : BitVec 64} : Match (loopEnv m0 m i ret) loopS m :=
  match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial
    ⟨by
      show BinOp.apply .add .W64 (reg m .rbx) (reg m .r12) = _ + BitVec.ofInt 64 0
      simp only [BinOp.apply, low_W64, ext_W64, hrbx, hr12, Env.base_ofMachine_eq,
        List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some, Option.getD_some]
      rw [NativeRustcVmX64.Transcript.ofInt_zero64, BitVec.add_zero], trivial⟩

omit [Host] in
/-- Words before the window survive a change of the window. -/
theorem ws_window (g : Geo m0 bp B.length) (hi : i < (reg m0 .rdx).toNat) {d d' : DataMem}
    (h : NativeRustcVm.WordsAt d (reg m0 .rsi) (wordsFrom B c i))
    (hs : NativeRustcVm.SameOutside d d'
      (NativeRustcVm.InRange (reg m0 .rsi + BitVec.ofNat 64 (8 * i)) 8)) :
    NativeRustcVm.WordsAt d' (reg m0 .rsi) (wordsFrom B c i) := by
  have hw := window g hi
  have honw := g.onw
  unfold NativeRustcVm.NoWrap at honw
  refine NativeRustcVm.BytesAt.of_sameOutside h hs fun j hj hin ↦ ?_
  rw [List.length_flatMap] at hj
  simp only [NativeRustcVm.length_wordBytes, List.map_const', List.sum_replicate, smul_eq_mul,
    length_wordsFrom] at hj
  rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; rw [hw]; omega), hw,
    NativeRustcVm.toNat_add_ofNat (by omega)] at hin
  omega

omit [Host] in
/-- The output's bytes survive a change of the stack and the reader's cursor. -/
theorem ws_keep (g : Geo m0 bp B.length) {ws : List UInt64}
    (hl : ws.length ≤ (reg m0 .rdx).toNat) {d d' : DataMem}
    (h : NativeRustcVm.WordsAt d (reg m0 .rsi) ws) {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → NativeRustcVm.InRange (stackBelow m0 48) (48 + 8) q ∨
      NativeRustcVm.InRange (reg m0 .rdi) 24 q) :
    NativeRustcVm.WordsAt d' (reg m0 .rsi) ws := by
  have honw := g.onw
  unfold NativeRustcVm.NoWrap at honw
  refine NativeRustcVm.BytesAt.of_sameOutside h hs fun j hj hq ↦ ?_
  rw [List.length_flatMap] at hj
  simp only [NativeRustcVm.length_wordBytes, List.map_const', List.sum_replicate,
    smul_eq_mul] at hj
  have hin : NativeRustcVm.InRange (reg m0 .rsi) (8 * (reg m0 .rdx).toNat)
      (reg m0 .rsi + BitVec.ofNat 64 j) := NativeRustcVm.inRange_add (by omega) (by omega)
  rcases hR _ hq with h1 | h1
  · exact g.g.wS _ hin h1
  · exact g.g.wR _ hin h1

/-- **One word**: from the loop's head after `i` words, the next read and stored; back at the
head or done. -/
theorem step (hp : Placed code k) (hle : Spec (Labels.label NativeRustcVmX64.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost)
    (g : Geo m0 bp B.length) {st : MachineState} (hI : LInv (k := k) m0 bp B c i st) :
    Eventually (step1 Host.exe)
      (fun st' ↦ Done (k := k) m0 bp B c st' ∨ LInv (k := k) m0 bp B c (i + 1) st') st := by
  have hn := hI.lt
  have hfit := hI.fit
  have hst : StackOk m0 48 := g.g.st
  have h8n : 8 * (reg m0 .rdx).toNat < 2 ^ 64 := by
    have := g.oS; have := g.onw; have := hst.2.1
    unfold NativeRustcVm.Apart at *; unfold NativeRustcVm.NoWrap at *
    have := NativeRustcVmX64.stackBelow_toNat (m := m0) (n := 48) hst.1
    omega
  -- `b4`: `call Reader::le`.
  have hwf := loop_wf g hn hI.fr (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.ReaderWords.b4Offset + b4.length)).toBitVec)
  have hm := loop_match hI.fr hI.rbx hI.r12 (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.ReaderWords.b4Offset + b4.length)).toBitVec)
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) exit_b4 hwf (fun _ _ ↦ rfl) hI.pc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hws, hrdi, hrsi, hkeep⟩ := ok_b4
  have hf1 : Frame m0 48 slots 0 st1.data := Frame.of_block hI.fr hwf hm1 hmid slots_le
  have hs1 : NativeRustcVm.SameOutside st.data.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 48) 8) :=
    sameOutside_low hwf hm1 (r := 0) rfl (by decide) hws
  have hR1 := g.reader hI.rd fun q hq ↦ hs1 q fun h ↦ hq (.inl (inRange_mono h (by omega)))
  have hk1 : ∀ x ∈ [Reg64.rbx, .r12, .r14, .r15], reg st1.data x = reg st.data x :=
    fun x hx ↦ hm1.regs x _ (hkeep x hx)
  have hrdi1 : reg st1.data .rdi = reg m0 .rdi := (hm1.regs .rdi _ hrdi).trans hI.r14
  have hrsi1 : (reg st1.data .rsi).toNat = 8 := by
    rw [show reg st1.data .rsi = _ from hm1.regs .rsi _ hrsi]
    rfl
  refine le_call hle g.g (F := 48) le_rfl slots_le hf1 hR1 hrdi1 hrsi1 hpc1
    fun m2 hf2 hcs2 hs2 hrr2 ↦ ?_
  rcases readRes_cases hrr2 with ⟨_, hfail⟩ | ⟨hax, hv, hR2, -⟩
  · exact absurd (by omega) hfail
  have hk2 : ∀ x ∈ [Reg64.rbx, .r12, .r14, .r15], reg m2 x = reg st.data x := fun x hx ↦ by
    have hcs : calleeSaved x = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> rfl
    exact (hcs2 x hcs).trans (hk1 x hx)
  -- `b5`: the tag.
  refine fr_step hp hst (j := NativeRustcVmX64.Vm.ReaderWords.b5Offset) b5_in_code (by simp [b5]) exit_b5 nofun ok_b5.1
    (st := ⟨m2, _⟩) rfl hf2 fun st3 hf3 hd3 hm3 hpc3 ↦ ?_
  have hk3 : ∀ x ∈ [Reg64.rax, .rdx, .rbx, .r12, .r14, .r15], reg st3.data x = reg m2 x :=
    fun x hx ↦ hm3.regs x _ (ok_b5.2 x hx)
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, low_W64] at hpc3
  change st3.pc = if (!(reg m2 .rax == BitVec.ofNat 64 1)) = true then _ else _ at hpc3
  rw [hax] at hpc3
  simp only [show ((1 : BitVec 64) == BitVec.ofNat 64 1) = true from rfl, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, show k + NativeRustcVmX64.Vm.ReaderWords.b5Offset + b5.length = k + NativeRustcVmX64.Vm.ReaderWords.b6Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReaderWords.b5_next]] at hpc3
  -- `b6`: the store.
  have hrbx3 : reg st3.data .rbx = reg m0 .rsi := by
    rw [hk3 .rbx (by simp), hk2 .rbx (by simp), hI.rbx]
  have hr12_3 : reg st3.data .r12 = BitVec.ofNat 64 (8 * i) := by
    rw [hk3 .r12 (by simp), hk2 .r12 (by simp), hI.r12]
  have hwf6 := loop_wf g hn hf3 (ret := 0)
  have hm6 := loop_match hf3 hrbx3 hr12_3 (ret := 0)
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) exit_b6 hwf6 nofun hpc3 hm6
    fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hmid6, hmem6, hr12_6, hkeep6⟩ := ok_b6
  have hf4 : Frame m0 48 slots 8 st4.data := Frame.of_block hf3 hwf6 hm4 hmid6 slots_le
  have hword := wordAt_write hm4 (r := 1) (o := 0) (b := reg m0 .rsi + BitVec.ofNat 64 (8 * i))
    (sz := 8) rfl (by decide) (v := .reg .rdx)
    (fun t ht ↦ by
      have := findWrite_head (r := 1) (o := 0) (v := .reg .rdx) (ws := []) ht
      rw [hmem6]
      exact this)
  rw [off_zero, show UInt64.ofBitVec ((Sym.reg .rdx).eval (loopEnv m0 st3.data i 0)) =
    leAt B (c + 8 * i) 8 from by
      show UInt64.ofBitVec (reg st3.data .rdx) = _
      rw [hk3 .rdx (by simp), hv]] at hword
  have hs4 : NativeRustcVm.SameOutside st3.data.dmem st4.data.dmem
      (NativeRustcVm.InRange (reg m0 .rsi + BitVec.ofNat 64 (8 * i)) 8) :=
    sameOutside_region hwf6 hm4 (r := 1) rfl (by simp [hmem6])
  have hwin : ∀ q, NativeRustcVm.InRange (reg m0 .rsi + BitVec.ofNat 64 (8 * i)) 8 q →
      NativeRustcVm.InRange (reg m0 .rsi) (8 * (reg m0 .rdx).toNat) q := fun q h ↦
    NativeRustcVm.InRange.of_sub (o := 8 * i) (m := 8) h g.onw (by omega)
  -- The words, the reader, the changes.
  have hws4 : NativeRustcVm.WordsAt st4.data.dmem (reg m0 .rsi) (wordsFrom B c (i + 1)) := by
    rw [wordsFrom_succ]
    refine NativeRustcVm.wordsAt_append_iff.mpr ⟨?_, ?_⟩
    · refine ws_window g hn ?_ hs4
      rw [show st3.data.dmem = m2.dmem from hd3]
      refine ws_keep g (by rw [length_wordsFrom]; omega) ?_ hs2 fun q h ↦ .inr ?_
      · exact ws_keep g (by rw [length_wordsFrom]; omega) hI.ws hs1 fun q h ↦
          .inl (inRange_mono h (by omega))
      · exact NativeRustcVm.InRange.of_sub (o := 16) (m := 8) h g.g.rNw (by omega)
    · rw [length_wordsFrom]
      exact NativeRustcVm.wordsAt_singleton_iff.mpr hword
  have hR4 : ReaderAt st4.data.dmem (reg m0 .rdi) bp B (c + 8 * (i + 1)) := by
    rw [show c + 8 * (i + 1) = c + 8 * i + 8 by omega]
    exact g.reader (by rw [show st3.data.dmem = m2.dmem from hd3]; exact hR2) fun q hq ↦ hs4 q fun h ↦ hq (.inr (hwin q h))
  have c2 : Chg m0 m2 := chg_trans (chg_trans hI.chg hs1 fun q h ↦
    .inl (inRange_mono h (by omega))) hs2 fun q h ↦ .inr (.inl h)
  have c3 : Chg m0 st3.data := fun q hq ↦ by
    rw [show st3.data.dmem = m2.dmem from hd3]
    exact c2 q hq
  have hchg4 : Chg m0 st4.data := chg_trans c3 hs4 fun q h ↦ .inr (.inr (hwin q h))
  have hk4 : ∀ x ∈ [Reg64.rbx, .r14, .r15], reg st4.data x = reg st.data x := fun x hx ↦ by
    rw [show reg st4.data x = reg st3.data x from hm4.regs x _ (hkeep6 x hx),
      hk3 x (by simp only [List.mem_cons] at hx ⊢; tauto),
      hk2 x (by simp only [List.mem_cons] at hx ⊢; tauto)]
  have hr12_4 : reg st4.data .r12 = BitVec.ofNat 64 (8 * (i + 1)) := by
    rw [show reg st4.data .r12 = BinOp.apply .add .W64 (BitVec.ofNat 64 8) (reg st3.data .r12)
      from hm4.regs .r12 _ hr12_6, hr12_3]
    simp only [BinOp.apply, low_W64, ext_W64]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Width.bits]
    omega
  -- The loop's test.
  have hr15 : reg st3.data .r15 = BitVec.ofNat 64 (8 * (reg m0 .rdx).toNat) := by
    rw [hk3 .r15 (by simp), hk2 .r15 (by simp), hI.r15]
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, low_W64] at hpc4
  change st4.pc = if (!(reg st3.data .r15 == BinOp.apply .add .W64 (BitVec.ofNat 64 8)
    (reg st3.data .r12))) = true then _ else _ at hpc4
  have hsum : BinOp.apply .add .W64 (BitVec.ofNat 64 8) (reg st3.data .r12) =
      BitVec.ofNat 64 (8 * (i + 1)) := by
    rw [hr12_3]
    simp only [BinOp.apply, low_W64, ext_W64]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Width.bits]
    omega
  rw [hr15, hsum, hp.label NativeRustcVmX64.Vm.ReaderWords.label_4_at, show k + NativeRustcVmX64.Vm.ReaderWords.b6Offset + b6.length = k + NativeRustcVmX64.Vm.ReaderWords.b7Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReaderWords.b6_next]] at hpc4
  by_cases hlast : i + 1 = (reg m0 .rdx).toNat
  · have he : (BitVec.ofNat 64 (8 * (reg m0 .rdx).toNat) == BitVec.ofNat 64 (8 * (i + 1))) =
        true := by rw [hlast]; exact beq_self_eq_true _
    rw [he] at hpc4
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc4
    refine .done _ (.inl ⟨hpc4, hf4, hfit, ?_, ?_, hchg4⟩)
    · rw [← hlast]; exact hR4
    · rw [← hlast]; exact hws4
  · have he : (BitVec.ofNat 64 (8 * (reg m0 .rdx).toNat) == BitVec.ofNat 64 (8 * (i + 1))) =
        false := by
      rw [beq_eq_false_iff_ne]
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      omega
    rw [he] at hpc4
    simp only [Bool.not_false, ↓reduceIte] at hpc4
    exact .done _ (.inr ⟨hpc4, hf4, by omega, hfit, (hk4 .r14 (by simp)).trans hI.r14,
      (hk4 .rbx (by simp)).trans hI.rbx, hr12_4, (hk4 .r15 (by simp)).trans hI.r15, hR4, hws4,
      hchg4⟩)

end Loop

end

end NativeRustcVmX64.Wire.ReaderWords
