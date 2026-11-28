module

public import NativeRustcVmX64.Arrays.Common
public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Transcript.Arith
public import NativeRustcVmX64.Spec.Layout
public import NativeRustcVm.Layout.RepLemmas

/-!
# The layout's proofs: what they share (x86-64)

- `retS`: the state at a `ret` of a function without pushes, region 0 the return address at RSP.
- `leaf_ret`: a block ending in that `ret` (region 0 of its environment the return address at
  RSP, then `rest`), run in a state with the entry's RSP, callee-saved registers and return
  address and writing nothing, returns to the caller with the block's registers, memory
  unchanged. `rsp_ptr0`: RSP at such a block's start.
-/

namespace NativeRustcVmX64.Layout

open NativeRustcX64 NativeRustcX64.Sym

@[expose] public section

/-- At a `ret` without pushes: the return address (region 0, RSP). -/
def retS : SState := init [8] [(.rsp, .ptr 0 0)]

end

public section

/-- RSP at the entry's value: region 0's base of an environment whose region 0 is the return
address at RSP. -/
theorem rsp_ptr0 [Labels] {m0 st : MachineData} {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} (hsp : rspOf st = rspOf m0) :
    st.regs.get64 .rsp =
      (Sym.ptr 0 ((0 : Nat) : Int)).eval (Transcript.frameEnv m0 st 0 rest vars ret) := by
  rw [Transcript.eval_ptr0, NativeRustcVm.Transcript.off_zero]
  show rspOf st = _
  rw [hsp]
  simp [stackBelow]

theorem mem_of_keepsAll {S₀ S : SState} {rs : List Reg64}
    (h : Arrays.keepsAll S₀ S rs = true) : S.mem = [] := by
  simp only [Arrays.keepsAll, Bool.and_eq_true, List.isEmpty_iff] at h
  exact h.2

theorem natsOf_getD (m : MachineData) (a : BitVec 64) {n t : Nat} (ht : t < n) :
    (natsOf m a n).getD t 0 = (NativeRustcVm.wordOf m.dmem (a + BitVec.ofNat 64 (8 * t))).toNat := by
  simp [natsOf, NativeRustcVm.wordsOf, Array.getD, ht]

/-- **Where a block wrote**: each write in one of the regions `rs` lists (region, bound), below
its bound. -/
theorem written_in [Labels] {env : Env} {S : SState} (hwf : env.WF) {rs : List (Nat × Nat)}
    (hrs : ∀ e ∈ rs, ∃ sz, (env.regions[e.1]?).map (·.2) = some sz ∧ e.2 ≤ sz)
    (hw : ∀ w ∈ S.mem, ∃ e ∈ rs, w.r = e.1 ∧ w.off + w.n ≤ e.2) {p : BitVec 64}
    (h : Written env S p) : ∃ e ∈ rs, InRange (env.base e.1) e.2 p := by
  obtain ⟨w, hw', b, sz, hb, h1, h2⟩ := h
  obtain ⟨e, he, hr, hle⟩ := hw w hw'
  obtain ⟨sz', hsz', hle'⟩ := hrs e he
  rw [hr] at hb
  rw [hb] at hsz'
  have hss : sz = sz' := by simpa using hsz'
  subst hss
  have hnw := hwf.noWrap _ b sz hb
  have hbase : env.base e.1 = b := by rw [Env.base, hb]; rfl
  refine ⟨e, he, ?_⟩
  rw [hbase, Sym.inRange_iff (by omega)]
  omega

open NativeRustcVmX64.Arrays (Body freeRegs keepsRegs regs_eq_of free_mem written_region0
  not_inRange_above not_inRange_below inRange_stack stackBelow_toNat) in
/-- **A block ending in a call, and the call**: from a body, a block that writes only the frame
(region 0) below offset `L`, keeps the free callee-saved registers and leaves RSP at offset `0`
calls a function that changes memory only in the outputs and its `n` bytes of stack and keeps
the callee-saved registers; it returns to a body. -/
theorem body_after_call [Labels] {m0 st st1 st2 : MachineData} {F S L n : Nat}
    {slots : List (Nat × Reg64)} {oa : BitVec 64} {on : Nat} {rs : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S₀ S₁ : SState}
    (hb : Body m0 F S slots oa on st) (hS : StackOk m0 S) (hle : F + n ≤ S) (hF8 : L ≤ F)
    (hslots : ∀ p ∈ slots, L ≤ p.1 ∧ p.1 + 8 ≤ F)
    (hwf : (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret).WF)
    (hm₀ : Match (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret) S₀ st)
    (hm : Match (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret) S₁ st1)
    (hk : keepsRegs S₀ S₁ (freeRegs slots) = true)
    (hsp : S₁.reg .rsp = some (.ptr 0 0)) (hw : ∀ w ∈ S₁.mem, w.r = 0 ∧ w.off + w.n ≤ L)
    (hsv : Saved st1 st2) (hrsp : rspOf st2 = rspOf st1 + 8#64)
    (hso : SameOutside st1.dmem st2.dmem
      (fun p ↦ InRange oa on p ∨ InRange (stackBelow st1 n) n p))
    (hoa : ∀ p, InRange oa on p → ¬InRange (stackBelow m0 S) S p) :
    Body m0 F S slots oa on st2 := by
  have hS1 := hS.1
  have hS2 := hS.2.1
  have hr0 := (rspOf m0).isLt
  have hfb : (stackBelow m0 F).toNat = (rspOf m0).toNat - F := stackBelow_toNat (by omega)
  have hrsp1 : rspOf st1 = stackBelow m0 F := by
    show st1.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp]
    simp [Sym.eval]
  have hwr : ∀ p, Written (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret) S₁ p →
      InRange (stackBelow m0 F) L p := fun p h ↦ written_region0 rfl hwf (by omega) hw h
  have hcallee : ∀ p, InRange (stackBelow st1 n) n p → InRange (stackBelow m0 S) S p :=
    fun p h ↦ by
      unfold stackBelow at h
      rw [hrsp1] at h
      exact inRange_stack (n := n) (k := 0) hS1 hle (Nat.zero_le _) (by simpa using h)
  have hblock : ∀ p, InRange (stackBelow m0 F) L p → InRange (stackBelow m0 S) S p := fun p h ↦
    inRange_stack (F := F) (n := 0) (k := L) hS1 (by omega) hF8 (by simpa using h)
  refine ⟨?_, fun p hp i hi ↦ ?_, fun r hr hn ↦ ?_, fun p hp ↦ ?_,
    fun p h ↦ hsv.2 p (hm.kept hwf p (hb.kept p h))⟩
  · rw [hrsp, hrsp1]; rfl
  · simp only [List.length_map, List.length_range] at hi
    obtain ⟨h8, hF⟩ := hslots p hp
    have hnw : (stackBelow m0 F).toNat + (F + 8) ≤ 2 ^ 64 := by rw [hfb]; omega
    have hin : InRange (stackBelow m0 S) S (stackBelow m0 F + BitVec.ofNat 64 (p.1 + i)) :=
      inRange_stack (F := F) (n := 0) (k := F) hS1 (by omega) le_rfl (by
        simp only [Nat.zero_add, BitVec.sub_zero]
        rw [Sym.inRange_iff (by omega), toNat_add_ofNat _ _ (by omega)]
        omega)
    show st2.dmem.get? (stackBelow m0 F + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i) = _
    rw [addr_add, hso _ ?_, hm.get?_mem0 hwf ?_]
    · rw [← addr_add]; exact hb.frame p hp i hi
    · exact fun h ↦ not_inRange_above (k := L) (by omega) (by omega) (hwr _ h)
    · rintro (h | h)
      · exact hoa _ h hin
      · unfold stackBelow at h
        rw [hrsp1] at h
        exact not_inRange_below (by omega) (by omega) h
  · exact (hsv.1 r hr).trans ((regs_eq_of hm₀ hm hk r (free_mem hr hn)).trans (hb.regs r hr hn))
  · have hp' : ¬InRange oa on p ∧ ¬InRange (stackBelow m0 S) S p :=
      ⟨fun h ↦ hp (Or.inl h), fun h ↦ hp (Or.inr h)⟩
    rw [hso p fun h ↦ h.elim hp'.1 fun h ↦ hp'.2 (hcallee p h),
      hm.get?_mem0 hwf fun h ↦ hp'.2 (hblock p (hwr p h))]
    exact hb.same p hp

open NativeRustcVmX64.Arrays (Body freeRegs keepsRegs regs_eq_of free_mem) in
/-- **A block storing into region `r ≥ 1`** of a body's environment (the frame, then `rs`), inside
the outputs, keeping RSP and the free callee-saved registers, keeps the body. -/
theorem body_of_store [Labels] {m0 st st' : MachineData} {F S : Nat}
    {slots : List (Nat × Reg64)} {oa : BitVec 64} {on : Nat} {rs : List (BitVec 64 × Nat)}
    {r : Nat} {b : BitVec 64} {n : Nat} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {S₀ S₁ : SState} (hb : Body m0 F S slots oa on st)
    (hwf : (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret).WF)
    (hm₀ : Match (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret) S₀ st)
    (hm : Match (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret) S₁ st')
    (hk : keepsRegs S₀ S₁ (.rsp :: freeRegs slots) = true) (hr : 1 ≤ r)
    (hrb : rs[r - 1]? = some (b, n))
    (hw : ∀ w ∈ S₁.mem, w.r = r ∧ w.off + w.n ≤ n) (hin : ∀ p, InRange b n p → InRange oa on p)
    (hslots : ∀ p ∈ slots, p.1 + 8 ≤ F) : Body m0 F S slots oa on st' := by
  have he := regs_eq_of hm₀ hm hk
  have hrb' : (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret).regions[r]? =
      some (b, n) := by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    simpa using hrb
  have hwr : ∀ p, Written (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret) S₁ p →
      InRange b n p := fun p h ↦ Arrays.written_region hrb' hwf le_rfl hw h
  have hd := hwf.disjoint 0 r _ _ _ _ (by omega) rfl hrb'
  have hnw0 := hwf.noWrap 0 _ _ rfl
  have hnw1 := hwf.noWrap r _ _ hrb'
  refine ⟨?_, fun p hp i hi ↦ ?_, fun r' hr' hn ↦ ?_, fun p hp ↦ ?_,
    fun p h ↦ hm.kept hwf p (hb.kept p h)⟩
  · show reg st' .rsp = _
    rw [he .rsp (by simp)]; exact hb.rsp
  · simp only [List.length_map, List.length_range] at hi
    have := hslots p hp
    rw [addr_add, hm.get?_mem0 hwf fun h ↦ ?_, ← addr_add]
    · exact hb.frame p hp i hi
    · have h1 := hwr _ h
      rw [Sym.inRange_iff hnw1, toNat_add_ofNat _ _ (by omega)] at h1
      omega
  · rw [he r' (List.mem_cons_of_mem _ (free_mem hr' hn))]; exact hb.regs r' hr' hn
  · rw [hm.get?_mem0 hwf fun h ↦ hp (Or.inl (hin p (hwr p h)))]
    exact hb.same p hp

variable [Host] in
/-- **A function without calls, run to its `ret`** from a frame (region 0 the `F` bytes below the
entry's RSP and the return address, then `rest`): the block returns to the caller, RSP 8 above,
the entry's callee-saved registers, in a state the block's final symbolic state describes. -/
theorem leaf_run {F : Nat} {ds : List Directive} {j n o : Nat} {S S' : SState}
    {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} (hk : ds.IsInfixAt Host.prog j)
    (hx : exec ds S = some (S', .ret (.load 0 F 8))) (hepi : Transcript.EpiOk F [] S' = true)
    {m0 : MachineData} {st : MachineState} (hst : StackOk m0 n) (hF : F ≤ n)
    (hpc : st.pc = Host.addrOf j) (hf : Transcript.Frame m0 F [] o st.data)
    (hrest : ∀ x ∈ rest, NativeRustcVm.Mapped st.data.dmem x.1 x.2 ∧ NativeRustcVm.NoWrap x.1 x.2)
    (hap : ((stackBelow m0 F, F + 8) :: rest).Pairwise
      fun x y ↦ NativeRustcVm.Apart x.1 x.2 y.1 y.2)
    (hm : Match (Transcript.frameEnv m0 st.data F rest vars) S st.data)
    {Q : MachineData → Prop}
    (hQ : ∀ d : MachineData, Match (Transcript.frameEnv m0 st.data F rest vars) S' d → Q d) :
    Eventually (step1 Host.exe)
      (fun s ↦ s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧ Q s.data ∧ Saved m0 s.data)
      st := by
  have hwf := Transcript.frame_wf (m0 := m0) (d := st.data) (F := F) (rest := rest)
    (vars := vars) (ret := 0)
    ⟨NativeRustcVm.Transcript.Mapped.keeps (Transcript.frame_mapped hst hF) hf.kept,
      Transcript.frame_noWrap hst hF⟩ hrest hap
  refine exec_at hk hx hwf nofun hpc hm fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hsv3, hrsp3⟩ := Transcript.Frame.epilogue hf hwf hm3 hepi
  simp only [PcOk] at hpc3
  exact .done _ ⟨by rw [hpc3]; exact hf.load_ret hst hF, hrsp3, hQ _ hm3, hsv3⟩

variable [Host]

/-- **A function without pushes, at its `ret`**: a block run in the environment whose region 0
is the return address at RSP, then `rest` (writing nothing, restoring nothing, RSP above the
return address), in a state with the entry's RSP, callee-saved registers and return address,
returns to the caller, RSP 8 above, memory unchanged, the registers the block's. -/
theorem leaf_ret {ds : List Directive} {j n : Nat} {S S' : SState}
    {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} (hk : ds.IsInfixAt Host.prog j)
    (hx : exec ds S = some (S', .ret (.load 0 0 8)))
    (hepi : Transcript.EpiOk 0 [] S' = true) (hmem : S'.mem = []) {m0 : MachineData}
    {st : MachineState} (hst : StackOk m0 n) (hpc : st.pc = Host.addrOf j)
    (hs : Saved m0 st.data) (hsp : rspOf st.data = rspOf m0)
    (hret : ∀ i < 8, st.data.dmem.get? (rspOf m0 + BitVec.ofNat 64 i) =
      m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 i))
    (hrest : ∀ x ∈ rest, NativeRustcVm.Mapped st.data.dmem x.1 x.2 ∧ NativeRustcVm.NoWrap x.1 x.2)
    (hap : ((stackBelow m0 0, 0 + 8) :: rest).Pairwise
      fun x y ↦ NativeRustcVm.Apart x.1 x.2 y.1 y.2)
    (hm : Match (Transcript.frameEnv m0 st.data 0 rest vars) S st.data)
    {Q : MachineData → Prop}
    (hQ : ∀ d : MachineData, (∀ r v, S'.reg r = some v →
        reg d r = v.eval (Transcript.frameEnv m0 st.data 0 rest vars)) →
      d.dmem = st.data.dmem → Q d) :
    Eventually (step1 Host.exe)
      (fun s ↦ s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧ Q s.data ∧ Saved m0 s.data)
      st := by
  have hf : Transcript.Frame m0 0 [] 0 st.data := Transcript.Frame.of_saved hs hsp hret
  have hwf := Transcript.frame_wf (m0 := m0) (d := st.data) (F := 0) (rest := rest)
    (vars := vars) (ret := 0)
    ⟨NativeRustcVm.Transcript.Mapped.keeps (Transcript.frame_mapped hst (Nat.zero_le _)) hf.kept,
      Transcript.frame_noWrap hst (Nat.zero_le _)⟩ hrest hap
  refine exec_at hk hx hwf nofun hpc hm fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hsv3, hrsp3⟩ := Transcript.Frame.epilogue hf hwf hm3 hepi
  have hd3 : st3.data.dmem = st.data.dmem := hm3.dmem_eq hwf hmem
  simp only [PcOk] at hpc3
  exact .done _ ⟨by rw [hpc3]; exact hf.load_ret hst (Nat.zero_le _), hrsp3,
    hQ _ (fun r v h ↦ hm3.regs r v h) hd3, hsv3⟩

/-- `leaf_ret` from `retS`. -/
theorem leaf_retS {ds : List Directive} {j n : Nat} {S' : SState} (hk : ds.IsInfixAt Host.prog j)
    (hx : exec ds retS = some (S', .ret (.load 0 0 8)))
    (hepi : Transcript.EpiOk 0 [] S' = true) (hmem : S'.mem = []) {m0 : MachineData}
    {st : MachineState} (hst : StackOk m0 n) (hpc : st.pc = Host.addrOf j)
    (hs : Saved m0 st.data) (hsp : rspOf st.data = rspOf m0)
    (hret : ∀ i < 8, st.data.dmem.get? (rspOf m0 + BitVec.ofNat 64 i) =
      m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 i))
    {Q : MachineData → Prop}
    (hQ : ∀ d : MachineData, (∀ r v, S'.reg r = some v →
        reg d r = v.eval (Transcript.frameEnv m0 st.data 0 [])) →
      d.dmem = st.data.dmem → Q d) :
    Eventually (step1 Host.exe)
      (fun s ↦ s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧ Q s.data ∧ Saved m0 s.data)
      st :=
  leaf_ret hk hx hepi hmem hst hpc hs hsp hret (by simp) (List.pairwise_singleton _ _)
    (match_ofMachine ⟨rfl, trivial⟩ ⟨rsp_ptr0 hsp, trivial⟩ trivial trivial trivial) hQ

end

end NativeRustcVmX64.Layout
