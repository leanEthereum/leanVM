module

public import NativeRustcVmArm.Bus.Common
public import NativeRustcVmArm.Sumcheck.Ctx
public import NativeRustcVm.Transcript.Update
public import NativeRustcVmArm.Transcript.Glue

/-!
# The GKR walk's proofs: what they share

Frames are `NativeRustcVmArm.Ring.Fr`; callees' preconditions come from
`NativeRustcVmArm.Sumcheck.Ctx` (`Fr.at_`: a state of the frame is at the frame when the outputs
are apart from the round constants).

- `Fr.at_`, `ctx_of`: the frame as `Sumcheck.At`, the entry as `Sumcheck.Ctx`.
- `out_not_rc`, `out_not_frame`: an output is apart from the round constants and the frame.
- `Fr.callSpec`: a call from the frame, the callee's postcondition on its own entry.
- `Fr.runBlock`: a block of the frame without writes.
- `okWord_bit`: bit `0` of `okWord b` is `b`.
-/

namespace NativeRustcVmArm.Bus.Gkr

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeRustcVm.Transcript
open NativeVm.Model (TState)
open NativeRustcVmArm.Sumcheck (Ctx At)

public section

section
variable [Labels] {m0 m : MachineData} {t : BitVec 64} {a : DecArea} {N F : Nat}
  {slots : List (Nat × XReg)} {keep : List XReg} {outs : BitVec 64 → Prop}

/-- The entry's context. -/
theorem ctx_of {s : TState} (hS : StackOk m0 N) (hrc : RcAt m0 N) (hts : TStateAt m0.dmem t a s)
    (htok : TStateOk m0 t a N) (hF : F ≤ N) (h16 : F % 16 = 0) : Ctx m0 t a N F :=
  ⟨hS, hrc, htok, hts.footprint, hF, h16⟩

/-- A state of the frame is at the frame, where the outputs are apart from the round
constants. -/
theorem Fr.at_ (c : Ctx m0 t a N F) (h : Fr m0 F N slots keep outs m)
    (ho : ∀ q, outs q → ¬InRange rcAddr 192 q) : At m0 F m :=
  ⟨h.sp, h.kept, fun q hq ↦ h.same q fun h' ↦
    h'.elim (fun hs ↦ c.not_rc_stack hs hq) (fun ho' ↦ ho q ho' hq)⟩

/-- An output is apart from the round constants. -/
theorem out_not_rc {o : BitVec 64} {n : Nat} (c : Ctx m0 t a N F) (h : OutOk m0 t a o n N)
    {q : BitVec 64} (hq : InRange o n q) : ¬InRange rcAddr 192 q :=
  NativeRustcVm.Apart.not_inRange h.2.2.2.2.2 h.2.1 c.rc.2.1 hq

/-- An output is apart from the frame. -/
theorem out_not_frame {o : BitVec 64} {n : Nat} (c : Ctx m0 t a N F) (h : OutOk m0 t a o n N)
    {q : BitVec 64} (hq : InRange o n q) : ¬InRange (base m0 F) F q :=
  NativeRustcVm.Apart.not_inRange (apart_frame c.spN c.le h.2.2.2.2.1) h.2.1
    (base_noWrap (by have := c.spN; have := c.le; omega)) hq

/-- The `TState` is apart from the frame. -/
theorem tstate_not_frame (c : Ctx m0 t a N F) {q : BitVec 64} (hq : InRange t tstateBytes q) :
    ¬InRange (base m0 F) F q :=
  NativeRustcVm.Apart.not_inRange (apart_frame c.spN c.le c.tok.1) c.fp.1.2
    (base_noWrap (by have := c.spN; have := c.le; omega)) hq

/-- A byte of the frame is neither the `TState`'s nor its decoded area's. -/
theorem frame_not_tstate (c : Ctx m0 t a N F) {q : BitVec 64} (hq : InRange (base m0 F) F q) :
    ¬InRange t tstateBytes q ∧ ¬InRange a.words (8 * a.len) q := by
  have hs : InRange (stackBelow m0 N) N q := c.inRange_frame hq
  have hnw : NativeRustcVm.NoWrap (stackBelow m0 N) N := by
    unfold NativeRustcVm.NoWrap; rw [c.stk]; have := c.spN; have := Sumcheck.Ctx.sp_lt m0; omega
  exact ⟨NativeRustcVm.Apart.not_inRange c.tok.1.symm hnw c.fp.1.2 hs,
    NativeRustcVm.Apart.not_inRange c.tok.2.1.symm hnw c.fp.2.1.2 hs⟩

/-- A byte of the frame is not an output's. -/
theorem frame_not_out {o : BitVec 64} {n : Nat} (c : Ctx m0 t a N F) (h : OutOk m0 t a o n N)
    {q : BitVec 64} (hq : InRange (base m0 F) F q) : ¬InRange o n q :=
  fun ho ↦ out_not_frame c h ho hq

end

/-- **A call from the frame**: the callee's contract on the state at the call, its changes the
outputs and its stack. -/
theorem Fr.callSpec [Host] {m0 : MachineData} {F N : Nat} {slots : List (Nat × XReg)}
    {keep : List XReg} {outs : BitVec 64 → Prop} {l : Label} {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} {N' : Nat} {st : MachineState} {next : Int64}
    {R : MachineState → Prop} (h : Fr m0 F N slots keep outs st.data)
    (hN : N ≤ m0.regs.SP.toNat) (hle : F + N' ≤ N) (hkeep : ∀ r ∈ keep, calleeSaved r = true)
    (hsl : ∀ p ∈ slots, p.1 + 8 ≤ F) (hfr : ∀ q, outs q → ¬InRange (base m0 F) F q)
    (hspec : Spec (Labels.label l) P Q)
    (hpc : st.pc = Labels.label l ∧ retOf st.data = next) (hP : P st.data)
    (hQ : ∀ m', Q st.data m' → SameOutside st.data.dmem m'.dmem
      (fun q ↦ InRange (stackBelow st.data N') N' q ∨ outs q) ∧ Saved st.data m')
    (cont : ∀ m2, Fr m0 F N slots keep outs m2 → Q st.data m2 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st :=
  Eventually.bind (Spec.apply hspec hpc.1 hP) fun ⟨m2, pc⟩ ⟨hpc', hq⟩ ↦ by
    simp only at hpc' hq
    rw [hpc', hpc.2]
    obtain ⟨hs, hS⟩ := hQ _ hq
    exact cont m2 (h.call hN hle hkeep hsl (fun _ h ↦ h) hfr hS hs) hq hS.1

/-- **A call from the frame writing `X`**: the outputs, or `n` bytes of the frame at `o` below
the slots. The callee's changes go on to the continuation. -/
theorem Fr.callLocal [Host] {m0 : MachineData} {F N : Nat} {slots : List (Nat × XReg)}
    {keep : List XReg} {outs : BitVec 64 → Prop} {l : Label} {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} {N' : Nat} {st : MachineState} {next : Int64}
    {R : MachineState → Prop} {X : BitVec 64 → Prop} {o n : Nat}
    (h : Fr m0 F N slots keep outs st.data)
    (hN : N ≤ m0.regs.SP.toNat) (hle : F + N' ≤ N) (hkeep : ∀ r ∈ keep, calleeSaved r = true)
    (hsl : ∀ p ∈ slots, o + n ≤ p.1 ∧ p.1 + 8 ≤ F) (honF : o + n ≤ F)
    (hfr : ∀ q, outs q → ¬InRange (base m0 F) F q)
    (hX : ∀ q, X q → outs q ∨ InRange (base m0 F + BitVec.ofNat 64 o) n q)
    (hspec : Spec (Labels.label l) P Q)
    (hpc : st.pc = Labels.label l ∧ retOf st.data = next) (hP : P st.data)
    (hQ : ∀ m', Q st.data m' → SameOutside st.data.dmem m'.dmem
      (fun q ↦ InRange (stackBelow st.data N') N' q ∨ X q) ∧ Saved st.data m')
    (cont : ∀ m2, Fr m0 F N slots keep outs m2 → Q st.data m2 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      SameOutside st.data.dmem m2.dmem (fun q ↦ InRange (stackBelow st.data N') N' q ∨ X q) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st :=
  Eventually.bind (Spec.apply hspec hpc.1 hP) fun ⟨m2, pc⟩ ⟨hpc', hq⟩ ↦ by
    simp only at hpc' hq
    rw [hpc', hpc.2]
    obtain ⟨hs, hS⟩ := hQ _ hq
    refine cont m2 ?_ hq hS.1 hs
    have hsb := stackBelow_eq h.sp (N' := N') (by omega)
    have hnw : NoWrap (base m0 (F + N')) N' := by
      unfold NoWrap; rw [base_toNat (by omega)]; have := m0.regs.SP.toNat_lt; omega
    have hnwN := base_noWrap (m0 := m0) (F := N) hN
    have hF := base_noWrap (m0 := m0) (F := F) (by omega)
    have hbF := base_toNat (m0 := m0) (F := F) (by omega)
    have hbN := base_toNat (m0 := m0) (F := N) hN
    have hbFN := base_toNat (m0 := m0) (F := F + N') (by omega)
    have hlt := m0.regs.SP.toNat_lt
    unfold NoWrap at hF
    have hloc : (base m0 F + BitVec.ofNat 64 o).toNat = (base m0 F).toNat + o :=
      NativeRustcVm.toNat_add_ofNat (by omega)
    have hnwl : (base m0 F + BitVec.ofNat 64 o).toNat + n ≤ 2 ^ 64 := by rw [hloc]; omega
    refine h.step hS.2.1 (fun r hr ↦ hS.1 r (hkeep r hr)) hS.2.2 hs (fun q hq ↦ ?_) ?_
    · rcases hq with hq | hq
      · left
        rw [hsb, Sym.inRange_iff hnw, hbFN] at hq
        rw [Sym.inRange_iff hnwN, hbN]
        omega
      · rcases hX q hq with hq | hq
        · exact .inr hq
        · left
          rw [Sym.inRange_iff hnwl, hloc] at hq
          rw [Sym.inRange_iff hnwN, hbN]
          omega
    · intro p hp i hi hq
      obtain ⟨hp1, hp8⟩ := hsl p hp
      rw [NativeRustcVm.addr_add_add] at hq
      have hv : (base m0 F + BitVec.ofNat 64 (p.1 + i)).toNat = (base m0 F).toNat + (p.1 + i) :=
        NativeRustcVm.toNat_add_ofNat (by omega)
      have hin : InRange (base m0 F) F (base m0 F + BitVec.ofNat 64 (p.1 + i)) :=
        NativeRustcVm.inRange_add (by omega) (by omega)
      rcases hq with hq | hq
      · rw [hsb, Sym.inRange_iff hnw, hbFN, hv] at hq
        omega
      · rcases hX _ hq with hq | hq
        · exact hfr _ hq hin
        · rw [Sym.inRange_iff hnwl, hloc, hv] at hq
          omega

/-- **Bytes of the frame kept by a call** writing below the frame and `X`, apart from them. -/
theorem keep_frame {m0 st : MachineData} {F N' : Nat} {X : BitVec 64 → Prop} {d' : DataMem}
    (hsp : st.regs.SP.toBitVec = base m0 F) (hN : F + N' ≤ m0.regs.SP.toNat)
    (hs : SameOutside st.dmem d' (fun q ↦ InRange (stackBelow st N') N' q ∨ X q))
    {o : Nat} {bs : List UInt8} (hF : o + bs.length ≤ F)
    (hX : ∀ i < bs.length, ¬X (base m0 F + BitVec.ofNat 64 (o + i)))
    (h : NativeRustcVm.BytesAt st.dmem (base m0 F + BitVec.ofNat 64 o) bs) :
    NativeRustcVm.BytesAt d' (base m0 F + BitVec.ofNat 64 o) bs :=
  NativeRustcVm.BytesAt.of_sameOutside h hs fun i hi hq ↦ by
    rw [NativeRustcVm.addr_add_add] at hq
    rcases hq with hq | hq
    · have hsb := stackBelow_eq hsp (N' := N') hN
      have hnw : NoWrap (base m0 (F + N')) N' := by
        unfold NoWrap; rw [base_toNat (by omega)]; have := m0.regs.SP.toNat_lt; omega
      have hbF := base_toNat (m0 := m0) (F := F) (by omega)
      have hbFN := base_toNat (m0 := m0) (F := F + N') (by omega)
      have hv : (base m0 F + BitVec.ofNat 64 (o + i)).toNat = (base m0 F).toNat + (o + i) :=
        NativeRustcVm.toNat_add_ofNat (by have := m0.regs.SP.toNat_lt; omega)
      rw [hsb, Sym.inRange_iff hnw, hbFN, hv] at hq
      omega
    · exact hX i hi hq

/-- A byte of the frame outside `n` bytes of it at `o`. -/
theorem not_loc {m0 : MachineData} {F : Nat} (hF : F ≤ m0.regs.SP.toNat) {o n j : Nat}
    (hon : o + n ≤ F) (hj : j < F) (hd : j < o ∨ o + n ≤ j) :
    ¬InRange (base m0 F + BitVec.ofNat 64 o) n (base m0 F + BitVec.ofNat 64 j) := by
  have hbF := base_toNat (m0 := m0) (F := F) hF
  have := m0.regs.SP.toNat_lt
  have h1 : (base m0 F + BitVec.ofNat 64 o).toNat = (base m0 F).toNat + o :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  have h2 : (base m0 F + BitVec.ofNat 64 j).toNat = (base m0 F).toNat + j :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  rw [Sym.inRange_iff (by rw [h1]; omega), h1, h2]
  omega

/-- **A byte no write of a block covers**: at `j` in region `r`, every write of the block in
region `r` apart from it, every other one within its region (`sizes`). -/
theorem not_written [Labels] {env : Env} {S : SState} (hwf : env.WF) {sizes : List Nat}
    (hsz : env.regions.map Prod.snd = sizes) {r : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) {j : Nat} (hj : j < sz)
    (hw : ∀ w ∈ S.mem, (w.r = r ∧ (w.off + w.n ≤ j ∨ j < w.off)) ∨
      (w.r ≠ r ∧ w.off + w.n ≤ (sizes[w.r]?).getD 0)) :
    ¬Written env S (b + BitVec.ofNat 64 j) := by
  rintro ⟨w, hw', b', sz', hb', h1, h2⟩
  have hnw := hwf.noWrap r b sz hb
  rw [NativeRustcVm.toNat_add_ofNat (by omega)] at h1 h2
  rcases hw w hw' with ⟨hr, hd⟩ | ⟨hr, hle⟩
  · rw [hr, hb] at hb'
    cases hb'
    omega
  · have hs : sizes[w.r]? = some sz' := by
      rw [← hsz, List.getElem?_map, hb']
      rfl
    rw [hs] at hle
    have := hwf.disjoint w.r r b' b sz' sz hr hb' hb
    simp only [Option.getD_some] at hle
    omega

/-- **Bytes a block kept**: at `o` in region `r`, the block's writes apart from the `L` bytes
there. -/
theorem keep_block [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    (hwf : env.WF) {sizes : List Nat} (hsz : env.regions.map Prod.snd = sizes) {r : Nat}
    {b : BitVec 64} {sz : Nat} (hb : env.regions[r]? = some (b, sz)) {o L : Nat}
    (hL : o + L ≤ sz)
    (hw : ∀ w ∈ S.mem, (w.r = r ∧ (w.off + w.n ≤ o ∨ o + L ≤ w.off)) ∨
      (w.r ≠ r ∧ w.off + w.n ≤ (sizes[w.r]?).getD 0))
    {bs : List UInt8} (hbs : bs.length ≤ L)
    (h : NativeRustcVm.BytesAt env.mem0 (b + BitVec.ofNat 64 o) bs) :
    NativeRustcVm.BytesAt m.dmem (b + BitVec.ofNat 64 o) bs :=
  NativeRustcVm.BytesAt.of_sameOutside h (hm.sameOutside hwf) fun i hi ↦ by
    rw [NativeRustcVm.addr_add_add]
    refine not_written hwf hsz hb (by omega) fun w hw' ↦ ?_
    rcases hw w hw' with ⟨hr, hd⟩ | h'
    · exact .inl ⟨hr, by omega⟩
    · exact .inr h'

/-- **A block of the frame without writes**, run from `init [(F, true)] (.ptr 0 0)`: the frame
and the memory kept. -/
theorem Fr.runBlock [Host] {m0 m : MachineData} {F N : Nat} {slots : List (Nat × XReg)}
    {keep : List XReg} {outs : BitVec 64 → Prop} {ds : List Directive} {j : Nat} {S' : SState}
    {x : Exit} {R : MachineState → Prop} (hS : StackOk m0 N) (hF : F ≤ N) (h16 : F % 16 = 0)
    (h : Fr m0 F N slots keep outs m) (hk : ds.IsInfixAt Host.prog j)
    (hx : exec ds (init [(F, true)] (.ptr 0 0)) = some (S', x)) (hmem : S'.mem = [])
    (hsp : S'.sp = .ptr 0 0) (hkeep : keep.all (fun r ↦ S'.reg r == some (.reg r)) = true)
    (hkeep0 : keep.all (fun r ↦ (init [(F, true)] (.ptr 0 0)).reg r == some (.reg r)) = true)
    (cont : ∀ st, Fr m0 F N slots keep outs st.data → st.data.dmem = m.dmem →
      Match (Env.ofMachine m [(base m0 F, F)]) S' st.data →
      PcOk (Env.ofMachine m [(base m0 F, F)]) x (Host.addrOf (j + ds.length)) st →
      Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf j⟩ := by
  have hwf := Bus.wf_frame hS hF h.kept
  have hm := Bus.match_frame hS hF h16 h.sp
  refine exec_then hk hx hwf hm fun st hm' hpc ↦ ?_
  have hd : st.data.dmem = m.dmem := hm'.dmem_eq hwf hmem
  refine cont st (Fr.ofBlock h hm hm' hwf rfl hmem (by rw [hsp]; rfl) fun r hr ↦ ?_) hd hm' hpc
  exact ⟨.reg r, beq_iff_eq.mp (List.all_eq_true.mp hkeep0 r hr),
    beq_iff_eq.mp (List.all_eq_true.mp hkeep r hr)⟩

/-- A machine state at an address. -/
theorem at_pc [Host] {st : MachineState} {pc : Int64} (h : st.pc = pc) {R : MachineState → Prop}
    (H : Eventually (step1 Host.exe) R ⟨st.data, pc⟩) : Eventually (step1 Host.exe) R st := by
  obtain ⟨d, q⟩ := st
  simp only at h
  subst h
  exact H

/-- A state in the frame with a second region at the address `x` in register `r`. -/
theorem match_frameW [Labels] {m0 m : MachineData} {F N : Nat} (hS : StackOk m0 N) (hF : F ≤ N)
    (h16 : F % 16 = 0) (hsp : m.regs.SP.toBitVec = base m0 F) {r : XReg} {n : Nat}
    {x : BitVec 64} (hx : (m.regs.getXReg r).toBitVec = x) :
    Match (Env.ofMachine m [(base m0 F, F), (x, n)])
      (init [(F, true), (n, false)] (.ptr 0 0) [(r, .ptr 1 0)]) m := by
  subst hx
  exact Bus.match_frame2 hS hF h16 hsp

/-- An address `j` bytes above `a` is in the `n` bytes from `a` iff `j < n`. -/
theorem inRange_add_iff {a : BitVec 64} {n j : Nat} (hj : j < 2 ^ 64) :
    InRange a n (a + BitVec.ofNat 64 j) ↔ j < n := by
  unfold InRange
  rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]

/-- Bit `0` of `okWord b`'s low half is `b`. -/
theorem okWord_bit (b : Bool) : (low .W32 (okWord b).toBitVec).getLsbD 0 = b := by
  cases b <;> decide

/-- A register a block set to a register's value. -/
theorem reg_of [Labels] {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    {r r' : XReg} (hm : Match (Env.ofMachine m rs) S m') (h : S.reg r = some (.reg r')) :
    m'.regs.getXReg r = m.regs.getXReg r' :=
  UInt64.toBitVec_inj.mp (hm.regs r _ h)

/-- A register a block set to a literal. -/
theorem reg_lit [Labels] {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    {r : XReg} {n : Nat} (hm : Match (Env.ofMachine m rs) S m') (h : S.reg r = some (.lit n)) :
    (m'.regs.getXReg r).toBitVec = BitVec.ofNat 64 n :=
  hm.regs r _ h

/-- **A `GkrStateW` kept** where the memory changed apart from it. -/
theorem gkrStateWAt_keep {d d' : DataMem} {p : BitVec 64} {g : NativeVm.Model.GkrStateW}
    {R : BitVec 64 → Prop} (h : NativeRustcVm.Bus.GkrStateWAt d p g)
    (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → ¬InRange p NativeRustcVm.Bus.gkrStateBytes q) :
    NativeRustcVm.Bus.GkrStateWAt d' p g := by
  have hin : ∀ o, o < 1064 → ¬R (p + BitVec.ofNat 64 o) := fun o ho hr ↦
    hR _ hr (NativeRustcVm.inRange_add ho (by decide))
  obtain ⟨hsz, hv, hl, hw, he⟩ := h
  refine ⟨hsz, NativeRustcVm.BytesAt.of_sameOutside hv hs fun i hi ↦ hin i ?_, hl,
    NativeRustcVm.BytesAt.of_sameOutside hw hs fun i hi ↦ ?_,
    NativeRustcVm.BytesAt.of_sameOutside he hs fun i hi ↦ ?_⟩
  · rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hsz] at hi
    omega
  · rw [NativeRustcVm.length_wordBytes] at hi
    show ¬R (p + BitVec.ofNat 64 48 + BitVec.ofNat 64 i)
    rw [NativeRustcVm.addr_add_add]
    exact hin _ (by omega)
  · rw [NativeRustcVm.length_ewsBytes] at hi
    have hl' : (g.point.toList).length ≤ 63 := hl
    show ¬R (p + BitVec.ofNat 64 48 + BitVec.ofNat 64 8 + BitVec.ofNat 64 i)
    rw [NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add]
    exact hin _ (by omega)

end

end NativeRustcVmArm.Bus.Gkr
