module

public import NativeRustcVmArm.Field.Call

/-!
# Prologue and epilogue

`prologue`: the entry block, run from `frameS F`, stores the saved registers in the frame
(`Slots`) and leaves `Fr` with the state it ends in as `m1`. `epilogue`: the last block, run from
`epiS F`, restores them (`restores`) and returns with SP, the callee-saved registers and every byte
outside the `N` bytes below SP as at the entry.
-/

namespace NativeRustcVmArm.Field

open NativeRustcArm NativeRustcArm.Sym

public section

theorem ofInt_ofBytes_byteOf' (x : BitVec 64) :
    BitVec.ofInt 64 (Int.ofBytes ((List.range 8).map (byteOf x))) = x := by
  have := ofBytes_byteOf x 0 8
  simp only [Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at this
  rw [this, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  have := x.isLt
  omega

variable [Host] {m0 : MachineData} {F N : Nat} {used : List XReg}

/-- The frame's environment. -/
abbrev frameEnv (m0 m : MachineData) (F : Nat) : Env := Env.ofMachine m [(stackBelow m0 F, F)]

omit [Host] in
theorem Geo.frame_wf (g : Geo m0 F N) {m : MachineData} (hk : Kept m0.dmem m.dmem) :
    (frameEnv m0 m F).WF := by
  have hb := g.base_toNat
  have hn := g.sp_toNat
  have hle := g.le
  have hlt := m0.regs.SP.toNat_lt
  refine Env.wf_of
    ⟨⟨fun i hi ↦ hk _ (g.mapped (p := stackBelow m0 F + BitVec.ofNat 64 i) ?_ ?_), ?_⟩,
    trivial⟩ (List.pairwise_singleton _ _)
  · rw [add_ofNat_toNat (by omega), hb]; omega
  · rw [add_ofNat_toNat (by omega), hb]; omega
  · show (stackBelow m0 F).toNat + F ≤ 2 ^ 64
    omega

/-- **The prologue.** -/
theorem prologue (g : Geo m0 F N) {ds : List Directive} {k : Nat} {S' : SState} {x : Exit}
    {slots : List (XReg × Nat)} (hk : ds.IsInfixAt Host.prog k)
    (hrun : exec ds (frameS F) = some (S', x)) (hsp : S'.sp = .ptr 0 0)
    (hkeep : keepsExcept used S' = true) (hw : ∀ w ∈ S'.mem, w.r = 0 ∧ w.off + w.n ≤ F)
    (hslots : ∀ p ∈ slots, p.2 + 8 ≤ F ∧ ∀ i < 8, findWrite 0 (p.2 + i) S'.mem = some (.reg p.1, i))
    {R : MachineState → Prop}
    (cont : ∀ st, Match (frameEnv m0 m0 F) S' st.data →
      PcOk (frameEnv m0 m0 F) x (Host.addrOf (k + ds.length)) st →
      Fr m0 st.data F N used st.data → Slots m0 st.data F slots →
      Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m0, Host.addrOf k⟩ := by
  have hb := g.base_toNat
  have hn := g.sp_toNat
  have hle := g.le
  have hlt := m0.regs.SP.toNat_lt
  have hwf := g.frame_wf (m := m0) fun _ h ↦ h
  have hm : Match (frameEnv m0 m0 F) (frameS F) m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ by rw [hb]; have := g.ok.1; have := g.f16; omega, trivial⟩
      (by
        show m0.regs.SP.toBitVec = (frameEnv m0 m0 F).base 0 + BitVec.ofInt 64 (F : Int)
        rw [Env.base_ofMachine m0 _ _ rfl, BitVec.ofInt_natCast]
        exact (BitVec.sub_add_cancel _ _).symm)
      trivial trivial trivial trivial
  refine exec_then hk hrun hwf hm fun st hm' hpc ↦ cont st hm' hpc ?_ ?_
  · refine ⟨?_, fun r hr hu ↦ ?_, fun _ _ ↦ rfl, fun p hp ↦ ?_, hm'.kept hwf⟩
    · rw [hm'.sp, hsp]
      show (frameEnv m0 m0 F).base 0 + BitVec.ofInt 64 0 = _
      rw [Env.base_ofMachine m0 _ _ rfl]
      simp
    · exact UInt64.toBitVec_inj.mp (hm'.regs r _ (keepsExcept_reg hkeep hr hu))
    · refine hm'.get?_mem0 hwf fun ⟨w, hwm, b, sz, hbs, h1, h2⟩ ↦ hp ?_
      obtain ⟨hr, hwn⟩ := hw w hwm
      rw [hr] at hbs
      cases hbs
      rw [inRange_iff (by rw [g.below_toNat]; omega), g.below_toNat]
      omega
  · intro p hp
    obtain ⟨hle8, hf⟩ := hslots p hp
    exact ⟨hle8, hm'.bytesAt_write (r := 0) (sz := F) rfl hle8 hf⟩

omit [Host] in
/-- The epilogue's symbolic state describes a state between prologue and epilogue. -/
theorem match_epi [Labels] (g : Geo m0 F N) {m1 m : MachineData} (hF : Fr m0 m1 F N used m) :
    Match (frameEnv m0 m F) (epiS F) m :=
  match_ofMachine ⟨rfl, fun _ ↦ by rw [g.base_toNat]; have := g.ok.1; have := g.f16; omega, trivial⟩
    (by
      show m.regs.SP.toBitVec = (frameEnv m0 m F).base 0 + BitVec.ofInt 64 0
      rw [Env.base_ofMachine m _ _ rfl, hF.sp]
      simp)
    trivial trivial trivial trivial

/-- **The epilogue**, ending in any exit (a return, or a tail call). -/
theorem epilogue_gen (g : Geo m0 F N) {m1 m : MachineData} (hF : Fr m0 m1 F N used m)
    {slots : List (XReg × Nat)} (hsl : Slots m0 m1 F slots) {ds : List Directive} {k : Nat}
    {S' : SState} {x : Exit} (hk : ds.IsInfixAt Host.prog k)
    (hrun : exec ds (epiS F) = some (S', x))
    (hres : restores slots used S' = true) (hsp : S'.sp = .ptr 0 F) (hmem : S'.mem = []) :
    Eventually (step1 Host.exe) (fun st ↦
      PcOk (frameEnv m0 m F) x (Host.addrOf (k + ds.length)) st ∧ retOf st.data = retOf m0 ∧
      SameOutside m0.dmem st.data.dmem (InRange (stackBelow m0 N) N) ∧ Saved m0 st.data ∧
      Match (frameEnv m0 m F) S' st.data) ⟨m, Host.addrOf k⟩ := by
  have hb := g.base_toNat
  have hn := g.sp_toNat
  have hle := g.le
  have hlt := m0.regs.SP.toNat_lt
  have hwf := g.frame_wf hF.kept
  have hbase : (frameEnv m0 m F).base 0 = stackBelow m0 F := Env.base_ofMachine m _ _ rfl
  have hm : Match (frameEnv m0 m F) (epiS F) m := match_epi g hF
  -- A slot's load is the register at the entry.
  have hload : ∀ p ∈ slots, (frameEnv m0 m F).load 0 p.2 8 = (m0.regs.getXReg p.1).toBitVec := by
    intro p hmem
    obtain ⟨h8, hbs⟩ := hsl _ hmem
    rw [Env.load_of_bytesAt (bs := (List.range 8).map (byteOf (m0.regs.getXReg p.1).toBitVec))
      (by simp) ?_, ofInt_ofBytes_byteOf']
    intro i hi
    simp only [List.length_map, List.length_range] at hi
    rw [hbase, Env.ofMachine_mem0, addr_add, hF.frame _ (by omega), ← addr_add]
    exact hbs i (by simp [hi])
  simp only [restores, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at hres
  obtain ⟨⟨hsl', hx30⟩, hcs⟩ := hres
  have hslot : ∀ p ∈ slots, ∀ st : MachineState, Match (frameEnv m0 m F) S' st.data →
      st.data.regs.getXReg p.1 = m0.regs.getXReg p.1 := fun p hp st hm' ↦
    UInt64.toBitVec_inj.mp ((hm'.regs p.1 _ (hsl' p hp)).trans (hload p hp))
  have hreg : ∀ r, calleeSaved r = true → ∀ st : MachineState, Match (frameEnv m0 m F) S' st.data →
      st.data.regs.getXReg r = m0.regs.getXReg r := by
    intro r hr st hm'
    have := hcs r (mem_allXRegs r)
    simp only [hr, Bool.not_true, Bool.false_or, Bool.or_eq_true, List.any_eq_true, beq_iff_eq,
      Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at this
    rcases this with ⟨p, hp, he⟩ | ⟨hu, hS⟩
    · rw [← XReg.idx_inj he]
      exact hslot p hp st hm'
    · rw [← hF.regs r hr fun hu' ↦ hu r hu' rfl]
      exact UInt64.toBitVec_inj.mp (hm'.regs r _ hS)
  have h30 : ∀ st : MachineState, Match (frameEnv m0 m F) S' st.data →
      st.data.regs.X30 = m0.regs.X30 := by
    intro st hm'
    obtain ⟨p, hp, he⟩ := hx30
    have := hslot p hp st hm'
    rwa [XReg.idx_inj (r' := .X30) he] at this
  refine exec_at hk hrun hwf rfl hm fun st hm' hpc ↦
    .done _ ⟨hpc, ?_, ?_, ⟨fun r hr ↦ ?_, ?_, ?_⟩, hm'⟩
  · unfold retOf
    rw [h30 st hm']
  · intro p hp
    rw [hm'.get?_mem0 hwf fun ⟨w, hw, _⟩ ↦ by rw [hmem] at hw; cases hw]
    exact hF.same p hp
  · exact hreg r hr st hm'
  · apply UInt64.toBitVec_inj.mp
    rw [hm'.sp, hsp]
    show (frameEnv m0 m F).base 0 + BitVec.ofInt 64 (F : Int) = _
    rw [hbase, BitVec.ofInt_natCast]
    exact BitVec.sub_add_cancel _ _
  · intro p hp
    rw [hm'.get?_mem0 hwf fun ⟨w, hw, _⟩ ↦ by rw [hmem] at hw; cases hw]
    exact hF.kept p hp

/-- **The epilogue**, ending in `ret`. -/
theorem epilogue (g : Geo m0 F N) {m1 m : MachineData} (hF : Fr m0 m1 F N used m)
    {slots : List (XReg × Nat)} (hsl : Slots m0 m1 F slots) {ds : List Directive} {k : Nat}
    {S' : SState} (hk : ds.IsInfixAt Host.prog k) (hrun : exec ds (epiS F) = some (S', .ret))
    (hres : restores slots used S' = true) (hsp : S'.sp = .ptr 0 F) (hmem : S'.mem = []) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m0 ∧
      SameOutside m0.dmem st.data.dmem (InRange (stackBelow m0 N) N) ∧ Saved m0 st.data ∧
      Match (frameEnv m0 m F) S' st.data) ⟨m, Host.addrOf k⟩ :=
  Eventually.mono (epilogue_gen g hF hsl hk hrun hres hsp hmem)
    fun st ⟨hpc, hret, h⟩ ↦ ⟨by simp only [PcOk] at hpc; rw [hpc, hret], h⟩

/-- **A block without memory accesses** between prologue and epilogue, run from `regS`. -/
theorem block {m1 m : MachineData} (hF : Fr m0 m1 F N used m) {ds : List Directive} {k : Nat}
    {S' : SState} {x : Exit} (hk : ds.IsInfixAt Host.prog k) (hrun : exec ds regS = some (S', x))
    (hmem : S'.mem = []) (hsp : S'.sp = .sp) (hkeep : keepsExcept used S' = true)
    {R : MachineState → Prop}
    (cont : ∀ st, Match (Env.ofMachine m []) S' st.data →
      PcOk (Env.ofMachine m []) x (Host.addrOf (k + ds.length)) st →
      Fr m0 m1 F N used st.data → Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf k⟩ :=
  exec_then hk hrun (Env.wf_nil m) (match_nil m) fun st hm hpc ↦
    cont st hm hpc (hF.block hm hmem hsp hkeep)

/-- **A call** between prologue and epilogue, to a callee using `S` bytes of stack below the
frame. -/
theorem call {m1 : MachineData} {env : Env} {l : Label} {next : Int64} {st : MachineState}
    (g : Geo m0 F N) (hF : Fr m0 m1 F N used st.data) (hpc : PcOk env (.call l) next st)
    {S : Nat} (hS : F + S ≤ N) {P : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    (hspec : Spec (Labels.label l) P Q) (hP : StackOk st.data S → P st.data)
    (hQ : ∀ m m', Q m m' → SameOutside m.dmem m'.dmem (InRange (stackBelow m S) S) ∧ Saved m m')
    {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = next → Q st.data st'.data → Fr m0 m1 F N used st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st :=
  call_then hpc hspec (hP (hF.stackOk g hS)) fun st' hpc' hq ↦
    cont st' hpc' hq (hF.call g hS (hQ _ _ hq).2 (hQ _ _ hq).1)

end

end NativeRustcVmArm.Field
