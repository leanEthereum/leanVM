module

public import NativeRustcVmX64.Transcript.Callee
public import NativeRustcVmX64.Transcript.ReadScalars.Exec
public import NativeRustcVmX64.Transcript.Arith
public import NativeRustcVm.Transcript.Loop
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names

/-!
# `TState::read_scalars` on x86-64

**`readScalars_spec`**: AL becomes `readScalars n`'s `Some`/`None`, the `n` elements at RSI its
elements and the `TState` at RDI its state, given `read_scalar`'s contract. `b0` pushes R15 to RBX,
sets BL = `1` and tests `n`: `0` returns at once (`b7`). Otherwise `b1` sets the output's cursor
and end; the loop (`b2` to `b4`, `step`, invariant `Inv`) reads a scalar into the frame and stores
it at the cursor until the end (`b5`, `b7` return BL = `1`) or a rejection (`b6`, `b7` return
`0`).
-/

namespace NativeRustcVmX64.Transcript.ReadScalars

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TStateReadScalars
open NativeRustcVm.Transcript NativeVm.Model

@[expose] public section

/-- At the loop's head, `i` elements read and stored: the frame, the `TState` (R12), the output's
end (R14) and cursor (R15), the frame's output slot (R13), BL = `1`, the first `i` elements and the
state after them, nothing changed but the output, the `TState` and the stack. -/
structure Inv (m0 : MachineData) (a : DecArea) (s : TState) (i : Nat) (d : MachineData) : Prop where
  frame : Frame m0 80 slots 8 d
  r12 : reg d .r12 = reg m0 .rdi
  r14 : reg d .r14 = off (reg m0 .rsi) (16 * (reg m0 .rdx).toNat)
  r15 : reg d .r15 = off (reg m0 .rsi) (16 * i)
  r13 : reg d .r13 = off (stackBelow m0 80) 16
  rbx : (reg d .rbx).toNat % 256 = 1
  run : ∃ xs s', (pushes readScalar i).run s = some (xs, s') ∧
    NativeRustcVm.EWsAt d.dmem (reg m0 .rsi) xs.toList ∧ TStateAt d.dmem (reg m0 .rdi) a s'
  same : NativeRustcVm.SameOutside m0.dmem d.dmem (fun q ↦
    NativeRustcVm.InRange (reg m0 .rsi) (16 * (reg m0 .rdx).toNat) q ∨
      NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 readScalarsStack) readScalarsStack q)

end

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 80 := by decide

variable [Host] {k : Nat}

/-- An end (`b7`, after `b5` or `b6` or not), from a state `S` of the frame's environment. -/
theorem finish (hp : Placed code k) {m0 d : MachineData} (hst : StackOk m0 readScalarsStack)
    (hf : Frame m0 80 slots 8 d) {S S' : SState} {v : Sym}
    (hx : exec b7 S = some (S', .ret (.load 0 80 8))) (hE : EndOk S' v) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TStateReadScalars.b7Offset)) (hm : Match (frameEnv m0 d 80 [] (fun _ ↦ 0) 0) S st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧ rspOf st'.data = rspOf m0 + 8#64 ∧
      reg st'.data .rax = v.eval (frameEnv m0 d 80 [] (fun _ ↦ 0) 0) ∧
      st'.data.dmem = d.dmem ∧ Saved m0 st'.data) st := by
  obtain ⟨hepi, hmem, hrax⟩ := hE
  have hwf := frame_wf (m0 := m0) (d := d) (F := 80) (rest := []) (vars := fun _ ↦ 0) (ret := 0)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.kept, frame_noWrap hst (by decide)⟩
    (by simp) (List.pairwise_singleton _ _)
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) hx hwf nofun hpc hm
    fun st' hm' hpc' => ?_
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hf hwf hm' hepi
  simp only [PcOk] at hpc'
  exact .done _ ⟨by rw [hpc']; exact hf.load_ret hst (by decide), hrsp, hm'.regs .rax _ hrax,
    hm'.dmem_eq hwf hmem, hsv⟩

/-- **One round of the loop**: a scalar read and stored; the loop goes on, returns `1` at the end
or `0` on a rejection. -/
theorem step (hp : Placed code k)
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    {a : DecArea} {s : TState} {m0 : MachineData} (hpre : ReadScalarsPre a s m0) {i : Nat}
    (hi : i < (reg m0 .rdx).toNat) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TStateReadScalars.b2Offset))
    (hI : Inv m0 a s i st.data) :
    Eventually (step1 Host.exe) (fun st' ↦
      (st'.pc = retOf m0 ∧ rspOf st'.data = rspOf m0 + 8#64 ∧ ReadScalarsPost a s m0 st'.data) ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TStateReadScalars.b2Offset) ∧ i + 1 < (reg m0 .rdx).toNat ∧
        Inv m0 a s (i + 1) st'.data)) st := by
  obtain ⟨hst, hrc, hts, htok, ⟨hom, hon, hoT, hoA, hoS, hoR⟩, hgot⟩ := hpre
  set t := reg m0 .rdi with htdef
  set o := reg m0 .rsi with hodef
  set n := (reg m0 .rdx).toNat with hndef
  set fb := stackBelow m0 80 with hfb
  have hn : readScalarsStack ≤ (rspOf m0).toNat := hst.1
  have h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hst.2.1
  have hfnw : NativeRustcVm.NoWrap fb (80 + 8) := frame_noWrap hst (by decide)
  have hfnw80 : NativeRustcVm.NoWrap fb 80 := by unfold NativeRustcVm.NoWrap at hfnw ⊢; omega
  obtain ⟨⟨hTm, hTn⟩, ⟨hAm, hAn⟩, -⟩ := hts.footprint
  have hTn' : t.toNat + 760 ≤ 2 ^ 64 := hTn
  have hon' : o.toNat + 16 * n ≤ 2 ^ 64 := hon
  have hsnw := noWrap_stackBelow hst
  have hTF : NativeRustcVm.Apart t 760 fb (80 + 8) := apart_frame htok.1 hn (by decide)
  have hAF : NativeRustcVm.Apart a.words (8 * a.len) fb (80 + 8) :=
    apart_frame htok.2.1 hn (by decide)
  have hoF : NativeRustcVm.Apart o (16 * n) fb (80 + 8) := apart_frame hoS hn (by decide)
  have hRF : ∀ q, NativeRustcVm.InRange fb (80 + 8) q →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q :=
    fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart hTF hTn hfnw h hq,
      fun h ↦ not_inRange_of_apart hAF hAn hfnw h hq⟩
  have hfS : ∀ q, NativeRustcVm.InRange fb 80 q →
      NativeRustcVm.InRange (stackBelow m0 readScalarsStack) readScalarsStack q :=
    fun q h ↦ inRange_frame_stack h8 hn (by decide) h
  obtain ⟨hf, hx12, hx14, hx15, hx13, hxbx, ⟨xs, s', hrun, hews, hts'⟩, hsame⟩ := hI
  have hxs : xs.size = i := pushes_size hrun
  -- `b2`: `call read_scalar`, its output at `fb + 16`.
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 80) (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.TStateReadScalars.b2Offset + b2.length)).toBitVec)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.kept, hfnw⟩ (by simp)
    (List.pairwise_singleton _ _)
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf (fun _ _ ↦ rfl) hpc
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hf.rsp_eval, hx13.trans (eval_ptr0 16).symm, trivial⟩
      trivial trivial trivial) fun st3 hm3 hpc3 => ?_
  obtain ⟨hmid3, hws3, hx7₃, hx6₃, hx12₃, hx13₃, hx14₃, hx15₃, hx3₃⟩ := after_eq run_b2 ▸ ok_b2
  have hf3 : Frame m0 80 slots 0 st3.data := Frame.of_block hf hwf hm3 hmid3 slots_le
  have hs3 : NativeRustcVm.SameOutside st.data.dmem st3.data.dmem (NativeRustcVm.InRange fb 8) :=
    sameOutside_low hwf hm3 (r := 0) rfl (by decide) hws3
  have hsp3 : rspOf st3.data = fb := by rw [hf3.sp, off_zero]
  have hX7₃ : reg st3.data .rdi = off fb 16 := (hm3.regs .rdi _ hx7₃).trans (eval_ptr0 16)
  have hX6₃ : reg st3.data .rsi = t := (hm3.regs .rsi _ hx6₃).trans hx12
  -- `read_scalar`.
  have hrcOut : ∀ q, (NativeRustcVm.InRange o (16 * n) q ∨ NativeRustcVm.InRange t tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 readScalarsStack) readScalarsStack q) →
      ¬ NativeRustcVm.InRange rcAddr 192 q := by
    rintro q (hq | hq | hq) h
    · exact not_inRange_of_apart (Apart.symm' hoR) hrc.2.1 hon h hq
    · exact not_inRange_of_apart (Apart.symm' htok.2.2) hrc.2.1 hTn h hq
    · exact not_inRange_of_apart hrc.2.2 hrc.2.1 hsnw h (inRange_mono hq (by omega))
  have hso3 : NativeRustcVm.SameOutside m0.dmem st3.data.dmem (fun q ↦
      NativeRustcVm.InRange o (16 * n) q ∨ NativeRustcVm.InRange t tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 readScalarsStack) readScalarsStack q) :=
    fun q hq ↦ by
      rw [hs3 q fun h ↦ hq (Or.inr (Or.inr (hfS q (inRange_mono h (by decide)))))]
      exact hsame q hq
  have hts3 : TStateAt st3.data.dmem t a s' :=
    hts'.frame (hm3.kept hwf) (fun q hq ↦ hRF q (inRange_mono hq (by decide))) hs3
  have hpre3 : ReadScalarPre a s' st3.data := by
    unfold ReadScalarPre
    rw [hX6₃, hX7₃]
    refine ⟨stackOk_callee hst hf3.kept hsp3 (by decide),
      RcAt.callee hrc (rc_keep hso3 hrcOut) hsp3 hn (by decide), hts3,
      TStateOk.callee htok hsp3 hn (by decide),
      OutOk.frame hst (by decide) hsp3 hf3.kept (by decide) (by decide) htok hrc, ?_⟩
    refine got_callee hgot (got_keep hgot hst (writes := [(o, 16 * n), (t, tstateBytes)])
      (by
        intro b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl <;> simp [o, n, t])
      (by
        intro b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · exact hon
        · exact hTn)
      (by simpa [or_assoc] using hso3))
      hsp3 hn (by decide) ?_
    intro l hl b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact (hgot.1 l hl).2.2.2 (t, tstateBytes) (by simp [t])
    · exact (hgot.1 l hl).2.2.2 (a.words, 8 * a.len) (by simp)
    · exact got_apart_frame hgot hst hl (ob := 16) (len := 24) (by decide) (by decide)
    · exact (hgot.1 l hl).2.2.2 (rcAddr, 192) (by simp)
  refine call_then hpc3 (hrs a s') hpre3 fun st4 hpc4 hrsp4 ⟨hout4, hnext4, hs4, hsv4⟩ => ?_
  rw [hX7₃] at hout4
  rw [hX6₃] at hnext4
  rw [hX7₃, hX6₃] at hs4
  have hcal4 : ∀ q, NativeRustcVm.InRange (stackBelow st3.data readScalarStack) readScalarStack q →
      NativeRustcVm.InRange (stackBelow m0 readScalarsStack) readScalarsStack q ∧
        ¬ NativeRustcVm.InRange fb (80 + 8) q :=
    fun q hq ↦ inRange_callee hsp3 h8 hn (by decide) hq
  have hslot : ∀ j, 16 + 24 ≤ j → j < 80 + 8 → ∀ q, q = off fb j →
      ¬ (NativeRustcVm.InRange (off fb 16) 24 q ∨ NativeRustcVm.InRange t tstateBytes q ∨
        NativeRustcVm.InRange (stackBelow st3.data readScalarStack) readScalarStack q) := by
    rintro j hj1 hj2 q rfl (h | h | h)
    · rw [inRange_off_iff (by omega) (by omega)] at h; omega
    · exact not_inRange_of_apart hTF hTn hfnw h (inRange_off_self hj2 (by omega))
    · exact (hcal4 _ h).2 (inRange_off_self hj2 (by omega))
  have hf4 : Frame m0 80 slots 8 st4.data :=
    Frame.call_slots hf3 hsv4 hrsp4 hs4
      (fun p hp i hi ↦ hslot _ (by
        simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)
        (by have := slots_le p hp; omega) _ rfl)
      (fun j hj ↦ hslot _ (by omega) (by omega) _ rfl)
  have hso4 : NativeRustcVm.SameOutside m0.dmem st4.data.dmem (fun q ↦
      NativeRustcVm.InRange o (16 * n) q ∨ NativeRustcVm.InRange t tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 readScalarsStack) readScalarsStack q) :=
    fun q hq ↦ by
      simp only [not_or] at hq
      have hqf : ¬ NativeRustcVm.InRange fb 80 q := fun h ↦ hq.2.2 (hfS q h)
      rw [hs4 q (by
        rintro (h | h | h)
        · exact hqf (inRange_of_off hfnw80 (by decide) h)
        · exact hq.2.1 h
        · exact hq.2.2 (hcal4 q h).1)]
      exact hso3 q (by simp only [not_or]; exact hq)
  have hlen : 16 * xs.toList.length ≤ 16 * n := by
    rw [Array.length_toList, hxs]; omega
  have hews3 : NativeRustcVm.EWsAt st3.data.dmem o xs.toList :=
    ewsAt_keep hs3 (by omega) (fun q hq hr ↦ not_inRange_of_apart hoF hon hfnw
      (inRange_mono hq hlen) (inRange_mono hr (by decide))) hews
  have hews4 : NativeRustcVm.EWsAt st4.data.dmem o xs.toList := by
    refine ewsAt_keep hs4 (by omega) (fun q hq hr ↦ ?_) hews3
    have hq' : NativeRustcVm.InRange o (16 * n) q := inRange_mono hq hlen
    rcases hr with hr | hr | hr
    · exact not_inRange_of_apart hoF hon hfnw hq' (inRange_mono
        (inRange_of_off hfnw80 (by decide) hr) (by decide))
    · exact not_inRange_of_apart hoT hon hTn hq' hr
    · exact not_inRange_of_apart hoS hon hsnw hq' (inRange_mono (hcal4 q hr).1 (by omega))
  have hsv34 : ∀ r, calleeSaved r = true → (after b2 callS).reg r = some (.reg r) →
      reg st4.data r = reg st.data r := fun r hr h ↦ (hsv4.1 r hr).trans (hm3.regs r _ h)
  have hX12₄ : reg st4.data .r12 = t := (hsv34 .r12 rfl hx12₃).trans hx12
  have hX14₄ : reg st4.data .r14 = off o (16 * n) := (hsv34 .r14 rfl hx14₃).trans hx14
  have hX15₄ : reg st4.data .r15 = off o (16 * i) := (hsv34 .r15 rfl hx15₃).trans hx15
  have hX3₄ : reg st4.data .rbx = reg st.data .rbx := hsv34 .rbx rfl hx3₃
  have hX13₄ : reg st4.data .r13 = off fb 16 :=
    (hsv4.1 .r13 rfl).trans ((hm3.regs .r13 _ hx13₃).trans (eval_ptr0 16))
  -- `b3`: the tag.
  have hwf4 := frame_wf (m0 := m0) (d := st4.data) (F := 80) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨Mapped.keeps (frame_mapped hst (by decide)) hf4.kept, hfnw⟩ (by simp)
    (List.pairwise_singleton _ _)
  have hm4 : Match (frameEnv m0 st4.data 80 [] (fun _ ↦ 0) 0) doneS st4.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hf4.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf4 nofun
    (hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateReadScalars.b2_next)) hm4 fun st5 hm5 hpc5 => ?_
  obtain ⟨hmid5, hmem5, hx12₅, hx13₅, hx14₅, hx15₅, hx3₅⟩ := after_eq run_b3 ▸ ok_b3
  simp only [PcOk] at hpc5
  sym_simp_at hpc5
  cases hr : readScalar.run s' with
  | none =>
    -- A rejection: `0`.
    rw [hr] at hout4
    have h0 : NativeRustcVm.WordAt st4.data.dmem (off fb 16) 0 := hout4
    have ht0 : (frameEnv m0 st4.data 80 [] (fun _ ↦ 0) 0).load 0 16 4 = BitVec.ofNat 64 0 :=
      load4_of_tag (Or.inl rfl) h0
    simp only [ht0] at hpc5
    simp (config := { decide := true }) only [↓reduceIte] at hpc5
    have hnone : (readScalars n).run s = none := pushes_none_of hrun hr n hi
    refine exec_at (infix_of b6_in_code (by simp [b6]) hp) exit_b6 hwf4 nofun
      (hpc5.trans (hp.label NativeRustcVmX64.Vm.TStateReadScalars.label_4_at)) hm5 fun st6 hm6 hpc6 => ?_
    refine Eventually.mono (finish hp hst hf4 exit_b7r end_r
      (hpc6.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateReadScalars.b6_next)) hm6)
      fun st' ⟨hpc', hrsp', hrax', hd', hsv'⟩ ↦ Or.inl ⟨hpc', hrsp', ?_, ?_, ?_, ?_, hsv'⟩
    · show (reg st'.data .rax).toNat % 256 = (okWord ((readScalars n).run s).isSome).toNat
      rw [hnone, hrax']; rfl
    · intro xs' s'' h; rw [hnone] at h; cases h
    · intro x' s'' h; rw [hnone] at h; cases h
    · intro q hq; rw [hd']; exact hso4 q hq
  | some p =>
  obtain ⟨x, s''⟩ := p
  rw [hr] at hout4
  obtain ⟨ht1, hel⟩ := (hout4 : OptEWAt st4.data.dmem (off fb 16) (some x))
  rw [ewAt_iff, off_off, off_off] at hel
  have hts4 : TStateAt st4.data.dmem t a s'' := hnext4 x s'' hr
  have ht1' : (frameEnv m0 st4.data 80 [] (fun _ ↦ 0) 0).load 0 16 4 = BitVec.ofNat 64 1 :=
    load4_of_tag (Or.inr rfl) ht1
  simp only [ht1'] at hpc5
  simp (config := { decide := true }) only [↓reduceIte] at hpc5
  have hf5 : Frame m0 80 slots 8 st5.data := Frame.of_block hf4 hwf4 hm5 hmid5 slots_le
  have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq hwf4 hmem5
  -- `b4`: the element stored at the cursor, the cursor advanced.
  set w := off o (16 * i) with hw
  have hwn : w.toNat = o.toNat + 16 * i := toNat_off (by omega)
  have hwF : NativeRustcVm.Apart fb (80 + 8) w 16 := by
    have h : o.toNat + 16 * n ≤ fb.toNat ∨ fb.toNat + (80 + 8) ≤ o.toNat := hoF
    show fb.toNat + (80 + 8) ≤ w.toNat ∨ w.toNat + 16 ≤ fb.toNat
    omega
  have hwf5 := frame_wf (m0 := m0) (d := st5.data) (F := 80) (rest := [(w, 16)])
    (vars := fun _ ↦ 0) (ret := 0)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf5.kept, hfnw⟩
    (by
      intro y hy
      rw [List.mem_singleton] at hy
      subst hy
      exact ⟨Mapped.keeps (mapped_off hom (by omega)) hf5.kept,
        by show w.toNat + 16 ≤ 2 ^ 64; omega⟩)
    (List.pairwise_pair.mpr hwF)
  have hreg5 : ∀ r, (after b3 doneS).reg r = some (.reg r) → reg st5.data r = reg st4.data r :=
    fun r h ↦ hm5.regs r _ h
  have hm5' : Match (frameEnv m0 st5.data 80 [(w, 16)] (fun _ ↦ 0) 0) storeS st5.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨hf5.rsp_eval, known_ptr rfl ((hreg5 .r15 hx15₅).trans hX15₄), trivial⟩ trivial trivial
      trivial
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) exit_b4 hwf5 nofun
    (hpc5.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateReadScalars.b3_next)) hm5' fun st6 hm6 hpc6 => ?_
  obtain ⟨hmid6, hw0, hw1, hws6, hx15₆, hx12₆, hx13₆, hx14₆, hx3₆⟩ := after_eq run_b4 ▸ ok_b4
  have hf6 : Frame m0 80 slots 8 st6.data := Frame.of_block hf5 hwf5 hm6 hmid6 slots_le
  have hs6 : NativeRustcVm.SameOutside st5.data.dmem st6.data.dmem (NativeRustcVm.InRange w 16) :=
    sameOutside_region hwf5 hm6 (r := 1) rfl hws6
  have hel6 : NativeRustcVm.EWAt st6.data.dmem w x := by
    refine ewAt_iff.mpr ⟨?_, ?_⟩
    · have := wordAt_write hm6 (r := 1) (o := 0) (b := w) (sz := 16) rfl (by decide)
        (fun j hj ↦ by rw [Nat.zero_add]; exact hw0 j hj)
      rwa [off_zero, show (Sym.load 0 24 8).eval (frameEnv m0 st5.data 80 [(w, 16)] (fun _ ↦ 0) 0)
        = _ from load_ofMachine (o := 24) rfl (hd5 ▸ hel.1)] at this
    · have := wordAt_write hm6 (r := 1) (o := 8) (b := w) (sz := 16) rfl (by decide) hw1
      rwa [show (Sym.load 0 32 8).eval (frameEnv m0 st5.data 80 [(w, 16)] (fun _ ↦ 0) 0)
        = _ from load_ofMachine (o := 32) rfl (hd5 ▸ hel.2)] at this
  have hews6 : NativeRustcVm.EWsAt st6.data.dmem o (xs.push x).toList := by
    refine ewsAt_push.mpr ⟨ewsAt_keep hs6 (by omega) (fun q hq hr ↦ ?_) (hd5 ▸ hews4), ?_⟩
    · rw [Array.length_toList, hxs] at hq
      have hwnw : NativeRustcVm.NoWrap w 16 := by show w.toNat + 16 ≤ 2 ^ 64; omega
      have hon16 : NativeRustcVm.NoWrap o (16 * i) := by show o.toNat + 16 * i ≤ 2 ^ 64; omega
      rw [inRange_iff' hon16] at hq
      rw [inRange_iff' hwnw] at hr
      omega
    · rw [hxs]; exact hel6
  have hwo : ∀ q, NativeRustcVm.InRange w 16 q → NativeRustcVm.InRange o (16 * n) q := by
    intro q hq
    have hwnw : NativeRustcVm.NoWrap w 16 := by show w.toNat + 16 ≤ 2 ^ 64; omega
    rw [inRange_iff' hwnw] at hq
    rw [inRange_iff' hon]
    omega
  have hts6 : TStateAt st6.data.dmem t a s'' :=
    (hd5 ▸ hts4).frame (hm6.kept hwf5) (fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart hoT hon hTn
      (hwo q hq) h, fun h ↦ not_inRange_of_apart hoA hon hAn (hwo q hq) h⟩) hs6
  have hso6 : NativeRustcVm.SameOutside m0.dmem st6.data.dmem (fun q ↦
      NativeRustcVm.InRange o (16 * n) q ∨ NativeRustcVm.InRange t tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 readScalarsStack) readScalarsStack q) :=
    fun q hq ↦ by
      rw [hs6 q fun h ↦ hq (Or.inl (hwo q h)), hd5]
      exact hso4 q hq
  have hrun' : (pushes readScalar (i + 1)).run s = some (xs.push x, s'') := by
    rw [pushes_succ, hrun]
    show (readScalar.run s').map _ = _
    rw [hr]; rfl
  have hX15₆ : reg st6.data .r15 = off o (16 * (i + 1)) := by
    rw [show reg st6.data .r15 = _ from hm6.regs .r15 _ hx15₆]
    show w + BitVec.ofInt 64 16 = _
    rw [show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, hw, off_add,
      show 16 * i + 16 = 16 * (i + 1) by omega]
  have hreg6 : ∀ r, (after b4 storeS).reg r = some (.reg r) → (after b3 doneS).reg r = some (.reg r) →
      reg st6.data r = reg st4.data r := fun r h1 h2 ↦ (hm6.regs r _ h1).trans (hreg5 r h2)
  have hX14₅ : reg st5.data .r14 = off o (16 * n) := (hreg5 .r14 hx14₅).trans hX14₄
  have hX3₆ : reg st6.data .rbx = reg st.data .rbx := (hreg6 .rbx hx3₆ hx3₅).trans hX3₄
  -- The cursor against the end.
  have hcond : (SBool.cmp .eq .W64 (.ptr 1 16) (.reg .r14)).not.eval
      (frameEnv m0 st5.data 80 [(w, 16)] (fun _ ↦ 0) 0) = decide (i + 1 ≠ n) := by
    simp only [SBool.eval, CmpOp.apply, low_W64, Sym.eval, Env.ofMachine_regs]
    rw [show (frameEnv m0 st5.data 80 [(w, 16)] (fun _ ↦ 0) 0).base 1 = w from rfl,
      show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, hw, off_add,
      show 16 * i + 16 = 16 * (i + 1) by omega,
      show st5.data.regs.get64 .r14 = off o (16 * n) from hX14₅,
      show (off o (16 * (i + 1)) == off o (16 * n)) = decide (i + 1 = n) from by
        rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]; exact off_eq_iff hon' hi]
    by_cases h : i + 1 = n <;> simp [h]
  simp only [PcOk] at hpc6
  rw [hcond] at hpc6
  by_cases hlast : i + 1 = n
  · -- The end: BL = `1`.
    simp only [hlast, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      at hpc6
    have hrn : (readScalars n).run s = some (xs.push x, s'') := by
      rw [readScalars_eq, show n = i + 1 from hlast.symm]; exact hrun'
    have hwf6 := frame_wf (m0 := m0) (d := st6.data) (F := 80) (rest := []) (vars := fun _ ↦ 0)
      (ret := 0) ⟨Mapped.keeps (frame_mapped hst (by decide)) hf6.kept, hfnw⟩ (by simp)
      (List.pairwise_singleton _ _)
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) exit_b5 hwf6 nofun
      (hpc6.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateReadScalars.b4_next))
      (match_ofMachine ⟨rfl, trivial⟩ ⟨hf6.rsp_eval, trivial⟩ trivial trivial trivial)
      fun st7 hm7 hpc7 => ?_
    simp only [PcOk] at hpc7
    refine Eventually.mono (finish hp hst hf6 exit_b7e end_e
      (hpc7.trans (hp.label NativeRustcVmX64.Vm.TStateReadScalars.label_5_at)) hm7)
      fun st' ⟨hpc', hrsp', hrax', hd', hsv'⟩ ↦ Or.inl ⟨hpc', hrsp', ?_, ?_, ?_, ?_, hsv'⟩
    · show (reg st'.data .rax).toNat % 256 = (okWord ((readScalars n).run s).isSome).toNat
      rw [hrn, hrax']
      show (UnOp.apply .trunc .W32 (reg st6.data .rbx)).toNat % 256 = 1
      rw [trunc32_mod, hX3₆, hxbx]
    · intro xs' s3 h
      rw [hrn] at h
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
      rw [hd']; exact hews6
    · intro xs' s3 h
      rw [hrn] at h
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      rw [hd']; exact hts6
    · intro q hq; rw [hd']; exact hso6 q hq
  · simp only [hlast, ne_eq, not_false_eq_true, decide_true, ↓reduceIte] at hpc6
    exact .done _ (Or.inr ⟨hpc6.trans (hp.label NativeRustcVmX64.Vm.TStateReadScalars.label_2_at), by omega,
      ⟨hf6, (hreg6 .r12 hx12₆ hx12₅).trans hX12₄, (hreg6 .r14 hx14₆ hx14₅).trans hX14₄,
        hX15₆, (hreg6 .r13 hx13₆ hx13₅).trans hX13₄, by rw [hX3₆]; exact hxbx,
        ⟨_, _, hrun', hews6, hts6⟩, hso6⟩⟩)

/-- **`TState::read_scalars` meets its contract.** -/
theorem readScalars_spec (hp : Placed code k)
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (a : DecArea) (s : TState) :
    Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s) := by
  intro m0 hpre
  obtain ⟨hst, hrc, hts, htok, ⟨hom, hon, hoT, hoA, hoS, hoR⟩, -⟩ := id hpre
  set t := reg m0 .rdi with htdef
  set o := reg m0 .rsi with hodef
  set n := (reg m0 .rdx).toNat with hndef
  set fb := stackBelow m0 80 with hfb
  have hn : readScalarsStack ≤ (rspOf m0).toNat := hst.1
  have h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hst.2.1
  have hfnw : NativeRustcVm.NoWrap fb (80 + 8) := frame_noWrap hst (by decide)
  obtain ⟨⟨hTm, hTn⟩, ⟨hAm, hAn⟩, -⟩ := hts.footprint
  have hTF : NativeRustcVm.Apart t 760 fb (80 + 8) := apart_frame htok.1 hn (by decide)
  have hAF : NativeRustcVm.Apart a.words (8 * a.len) fb (80 + 8) :=
    apart_frame htok.2.1 hn (by decide)
  -- `b0`: the prologue, BL = `1`, `n = 0`?
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 80) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨frame_mapped hst (by decide), hfnw⟩ (by simp) (List.pairwise_singleton _ _)
  have hm0 : Match (frameEnv m0 m0 80 [] (fun _ ↦ 0) 0) entryS m0 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial trivial
  unfold NativeRustcVmX64.Vm.TStateReadScalars.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.TStateReadScalars.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 nofun hm0
    fun st1 hm1 hpc1 => ?_
  have hbx : ∀ {S : SState} {d : MachineData}, Match (frameEnv m0 m0 80 [] (fun _ ↦ 0) 0) S d →
      S.reg .rbx = some (.bin .merge .W8 (.reg .rbx) (.lit 1)) → (reg d .rbx).toNat % 256 = 1 :=
    fun hm h ↦ by rw [show reg _ .rbx = _ from hm.regs .rbx _ h]; exact merge_one_mod _
  simp only [PcOk] at hpc1
  split at hpc1
  · -- `n = 0`: `1`.
    rename_i hc
    have hn0 : n = 0 := by
      sym_simp_at hc
      simp only [Env.ofMachine_regs, BitVec.and_self, beq_iff_eq] at hc
      show (m0.regs.get64 .rdx).toNat = 0
      rw [hc]; rfl
    have hr0 : (readScalars n).run s = some (#[], s) := by
      rw [readScalars_eq, show n = 0 from hn0]; rfl
    obtain ⟨hpro, hws1, hrbx1⟩ := ok_b0
    have hf1 : Frame m0 80 slots 8 st1.data :=
      Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le (by decide)
    have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem (NativeRustcVm.InRange fb 80) :=
      sameOutside_low hwf0 hm1 (r := 0) rfl (by decide) hws1
    refine Eventually.mono (finish hp hst hf1 exit_b7 end_0 (hpc1.trans (hp.label NativeRustcVmX64.Vm.TStateReadScalars.label_5_at))
      (match_ofMachine ⟨rfl, trivial⟩ ⟨hf1.rsp_eval, trivial⟩ trivial trivial trivial))
      fun st' ⟨hpc', hrsp', hrax', hd', hsv'⟩ ↦ ⟨hpc', hrsp', ?_, ?_, ?_, ?_, hsv'⟩
    · show (reg st'.data .rax).toNat % 256 = (okWord ((readScalars n).run s).isSome).toNat
      rw [hr0, hrax']
      show (UnOp.apply .trunc .W32 (reg st1.data .rbx)).toNat % 256 = 1
      rw [trunc32_mod]; exact hbx hm1 hrbx1
    · intro xs s' h
      rw [hr0] at h
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
      exact ewsAt_nil _ _
    · intro xs s' h
      rw [hr0] at h
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      rw [hd']
      exact hts.frame hf1.kept (fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart hTF hTn hfnw h
        (inRange_mono hq (by decide)), fun h ↦ not_inRange_of_apart hAF hAn hfnw h
        (inRange_mono hq (by decide))⟩) hs1
    · intro q hq
      rw [hd']
      exact hs1 q fun h ↦ hq (Or.inr (Or.inr (inRange_frame_stack h8 hn (by decide) h)))
  rename_i hc
  have hn0 : n ≠ 0 := by
    intro h0
    apply hc
    sym_simp
    simp only [Env.ofMachine_regs, BitVec.and_self, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    exact h0
  -- `b1`: the output's cursor and end.
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf0 nofun
    (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateReadScalars.b0_next)) hm1 fun st2 hm2 hpc2 => ?_
  obtain ⟨hpro, hws2, hrbx2, hx14, hx15, hx12, hx13⟩ := ok_b1
  have hf2 : Frame m0 80 slots 8 st2.data :=
    Frame.of_prologue Frame.entry hwf0 hm2 hpro slots_le (by decide)
  have hs2 : NativeRustcVm.SameOutside m0.dmem st2.data.dmem (NativeRustcVm.InRange fb 80) :=
    sameOutside_low hwf0 hm2 (r := 0) rfl (by decide) hws2
  have hX14 : reg st2.data .r14 = off o (16 * n) := by
    rw [show reg st2.data .r14 = _ from hm2.regs .r14 _ hx14]
    simp only [endSym, Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    apply BitVec.eq_of_toNat_eq
    have e1 : (m0.regs.get64 .rsi).toNat = o.toNat := rfl
    have e2 : (m0.regs.get64 .rdx).toNat = n := rfl
    have : o.toNat + 16 * n ≤ 2 ^ 64 := hon
    simp only [off, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      show shiftCount .W64 (BitVec.ofNat 64 4) = 4 from rfl, Nat.shiftLeft_eq,
      show (2 : Nat) ^ Width.W64.bits = 2 ^ 64 from rfl, e1, e2]
    omega
  have hInv : Inv m0 a s 0 st2.data := by
    refine ⟨hf2, hm2.regs .r12 _ hx12, hX14,
      (hm2.regs .r15 _ hx15).trans (by rw [Nat.mul_zero, off_zero]; rfl),
      (hm2.regs .r13 _ hx13).trans (eval_ptr0 16), hbx hm2 hrbx2,
      ⟨#[], s, pushes_zero _ _, ewsAt_nil _ _, ?_⟩, fun q hq ↦ ?_⟩
    · exact hts.frame hf2.kept (fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart hTF hTn hfnw h
        (inRange_mono hq (by decide)), fun h ↦ not_inRange_of_apart hAF hAn hfnw h
        (inRange_mono hq (by decide))⟩) hs2
    · exact hs2 q fun h ↦ hq (Or.inr (Or.inr (inRange_frame_stack h8 hn (by decide) h)))
  refine loop (I := fun j st ↦ ∃ i, j = n - i ∧ i < n ∧ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TStateReadScalars.b2Offset) ∧
      Inv m0 a s i st.data)
    (fun j st ⟨i, hj, hi, hpc, hI⟩ ↦ Eventually.mono (step hp hrs hpre hi hpc hI) fun st' h ↦ ?_)
    ⟨0, rfl, by omega, hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateReadScalars.b1_next), hInv⟩
  rcases h with h | ⟨hpc', hlt, hI'⟩
  · exact Or.inl h
  · exact Or.inr ⟨n - (i + 1), by omega, i + 1, rfl, hlt, hpc', hI'⟩

end

end NativeRustcVmX64.Transcript.ReadScalars
