module

public import NativeRustcX64.Sym.Sound.Data
public import NativeRustcX64.Sym.Sound.Shift
public import NativeRustcX64.Sym.Sound.Control
public import NativeRustcX64.Sym.Sound.Carry
public import NativeRustcX64.Sym.Sound.Bit

/-!
# The symbolic executor is sound

`Sym.exec_sound`: where the symbolic executor runs a block `ds` placed at directive `k` of the
program from a symbolic state `S` to `S'` with exit `x`, the machine, from any state `S`
describes at the block's address, inevitably reaches a state `S'` describes, at the pc `x` says
(`PcOk`, with the address after the block for a fall-through or an untaken branch). A block that
ends in a call pushes the environment's return address `env.ret`, which must be the address after
the block. `Sym.match_init`: the initial symbolic state of a machine state describes it.
-/

namespace NativeRustcX64.Sym

public section

/-- Every instruction is sound. -/
theorem stepOp_ok [Labels] {env : Env} {w : Width} (op : Operation w) : OpOk env op := by
  cases op with
  | mov dst src => exact ok_mov dst src
  | movzx dst src => exact ok_movzx dst src
  | movsx dst src => exact ok_movsx dst src
  | push src => exact ok_push src
  | pop dst => exact ok_pop dst
  | setcc cc dst => exact ok_setcc cc dst
  | cmovcc cc dst src => exact ok_cmovcc cc dst src
  | lea dst a => exact ok_lea dst a
  | add dst src => exact ok_add dst src
  | sub dst src => exact ok_sub dst src
  | and dst src => exact ok_and dst src
  | or dst src => exact ok_or dst src
  | xor dst src => exact ok_xor dst src
  | cmp a b => exact ok_cmp a b
  | test a b => exact ok_test a b
  | inc dst => exact ok_inc dst
  | dec dst => exact ok_dec dst
  | neg dst => exact ok_neg dst
  | not dst => exact ok_not dst
  | imul dst src1 src2 => exact ok_imul dst src1 src2
  | mul src => exact ok_mul src
  | adc dst src => exact ok_adc dst src
  | sbb dst src => exact ok_sbb dst src
  | shl dst c => exact ok_shl dst c
  | shr dst c => exact ok_shr dst c
  | sar dst c => exact ok_sar dst c
  | rol dst c => exact ok_rol dst c
  | ror dst c => exact ok_ror dst c
  | shld dst src c => exact ok_shld dst src c
  | shrd dst src c => exact ok_shrd dst src c
  | bswap dst => exact ok_bswap dst
  | bt base offset => exact ok_bt base offset
  | bts base offset => exact ok_bts base offset
  | jcc cc l => exact ok_jcc cc l
  | jmp t => exact ok_jmp t
  | call t => exact ok_call t
  | ret => exact ok_ret
  | nop n => exact ok_nop n
  | nopalign a pad => exact ok_nopalign a pad
  | _ => intro _ _ _ _ _ _ _ h; cases h

section
variable [Host] {env : Env}

/-- One directive of a block: a label falls through, an instruction is sound. -/
theorem stepD_ok_ro {d : Directive} {p : Program} {k : Nat} (hdp : (d :: p).IsInfixAt Host.prog k)
    {S S' : SState} {x : Exit} {m : MachineData} (hwf : env.WFRo) (hm : Match env S m)
    (h : stepD d S = some (S', x))
    (hret : ∀ l, x = .call l → env.ret = (Host.addrOf k.succ).toBitVec) :
    Eventually (step1 Host.exe) (fun st => Match env S' st.data ∧
      PcOk env x (Host.addrOf k.succ) st) ⟨m, Host.addrOf k⟩ := by
  apply Host.eventually_of_interp hdp
  cases d with
  | label l =>
    cases h
    exact done_fall (p := ⟨Host.addrOf k, Host.addrOf k.succ⟩) hm
  | instr i =>
    cases i with
    | regular aw w op =>
      cases aw with
      | W64 => exact stepOp_ok op S S' x m ⟨Host.addrOf k, Host.addrOf k.succ⟩ hwf hm h hret
      | _ => cases h
    | avx _ _ _ => cases h
  | byteArray _ => cases h
  | word _ _ => cases h

theorem stepD_ok {d : Directive} {p : Program} {k : Nat} (hdp : (d :: p).IsInfixAt Host.prog k)
    {S S' : SState} {x : Exit} {m : MachineData} (hwf : env.WF) (hm : Match env S m)
    (h : stepD d S = some (S', x))
    (hret : ∀ l, x = .call l → env.ret = (Host.addrOf k.succ).toBitVec) :
    Eventually (step1 Host.exe) (fun st => Match env S' st.data ∧
      PcOk env x (Host.addrOf k.succ) st) ⟨m, Host.addrOf k⟩ :=
  stepD_ok_ro hdp hwf.toWFRo hm h hret

/-- **The symbolic executor is sound** under `Env.WFRo`. -/
theorem exec_sound_ro {ds : List Directive} {k : Nat} (hk : ds.IsInfixAt Host.prog k)
    {S S' : SState} {x : Exit} (hx : exec ds S = some (S', x)) (hwf : env.WFRo)
    (hret : ∀ l, x = .call l → env.ret = (Host.addrOf (k + ds.length)).toBitVec)
    {m : MachineData} (hm : Match env S m) :
    Eventually (step1 Host.exe) (fun st => Match env S' st.data ∧
      PcOk env x (Host.addrOf (k + ds.length)) st) ⟨m, Host.addrOf k⟩ := by
  induction ds generalizing k S m with
  | nil =>
    cases hx
    exact Eventually.done _ ⟨hm, rfl⟩
  | cons d ds ih =>
    have hd' := hk.cons
    cases hd : stepD d S with
    | none => simp [exec, hd] at hx
    | some r =>
      obtain ⟨S₁, x₁⟩ := r
      cases x₁ with
      | fall =>
        simp only [exec, hd] at hx
        have hlen : k + 1 + ds.length = k + (d :: ds).length := by
          simp [Nat.add_assoc, Nat.add_comm 1]
        refine eventually_trans _ _ _ _ (stepD_ok_ro hk hwf hm hd nofun) fun st ⟨hm₁, hpc⟩ => ?_
        obtain ⟨m₁, pc⟩ := st
        simp only [PcOk] at hpc
        subst hpc
        have := ih hd'.2 hx (by rw [hlen]; exact hret) hm₁
        rwa [hlen] at this
      | _ =>
        cases ds with
        | cons _ _ => simp [exec, hd] at hx
        | nil =>
          simp only [exec, hd, Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          exact stepD_ok_ro hk hwf hm hd hret

/-- **The symbolic executor is sound.** Where it runs the block `ds`, placed at directive `k`
of the program, from `S` to `S'` with exit `x`, the machine inevitably goes from any state `S`
describes at the block's address to a state `S'` describes, at the pc `x` says; a block ending in
a call needs `env.ret` to be the address after it. -/
theorem exec_sound {ds : List Directive} {k : Nat} (hk : ds.IsInfixAt Host.prog k)
    {S S' : SState} {x : Exit} (hx : exec ds S = some (S', x)) (hwf : env.WF)
    (hret : ∀ l, x = .call l → env.ret = (Host.addrOf (k + ds.length)).toBitVec)
    {m : MachineData} (hm : Match env S m) :
    Eventually (step1 Host.exe) (fun st => Match env S' st.data ∧
      PcOk env x (Host.addrOf (k + ds.length)) st) ⟨m, Host.addrOf k⟩ :=
  exec_sound_ro hk hx hwf.toWFRo hret hm

end

section
variable [ElfHost] {env : Env}

/-- One directive of a block inside section `sec` of a multi-section `ElfHost`. -/
theorem stepD_ok_elf_ro {sec : Nat} {d : Directive} {p : Program} {k : Nat}
    (hdp : (d :: p).IsInfixAt (ElfHost.sectionProg sec) k)
    {S S' : SState} {x : Exit} {m : MachineData} (hwf : env.WFRo) (hm : Match env S m)
    (h : stepD d S = some (S', x))
    (hret : ∀ l, x = .call l → env.ret = (ElfHost.addrOf sec k.succ).toBitVec) :
    Eventually (elfStep1 ElfHost.exe) (fun st => Match env S' st.data ∧
      PcOk env x (ElfHost.addrOf sec k.succ) st) ⟨m, ElfHost.addrOf sec k⟩ := by
  apply ElfHost.eventually_of_interp hdp
  cases d with
  | label l =>
    cases h
    exact done_fall (p := ⟨ElfHost.addrOf sec k, ElfHost.addrOf sec k.succ⟩) hm
  | instr i =>
    cases i with
    | regular aw w op =>
      cases aw with
      | W64 => exact stepOp_ok op S S' x m ⟨ElfHost.addrOf sec k, ElfHost.addrOf sec k.succ⟩ hwf hm h hret
      | _ => cases h
    | avx _ _ _ => cases h
  | byteArray _ => cases h
  | word _ _ => cases h

theorem stepD_ok_elf {sec : Nat} {d : Directive} {p : Program} {k : Nat}
    (hdp : (d :: p).IsInfixAt (ElfHost.sectionProg sec) k)
    {S S' : SState} {x : Exit} {m : MachineData} (hwf : env.WF) (hm : Match env S m)
    (h : stepD d S = some (S', x))
    (hret : ∀ l, x = .call l → env.ret = (ElfHost.addrOf sec k.succ).toBitVec) :
    Eventually (elfStep1 ElfHost.exe) (fun st => Match env S' st.data ∧
      PcOk env x (ElfHost.addrOf sec k.succ) st) ⟨m, ElfHost.addrOf sec k⟩ :=
  stepD_ok_elf_ro hdp hwf.toWFRo hm h hret

/-- **The symbolic executor is sound under a multi-section `ElfHost` and `Env.WFRo`.** -/
theorem exec_sound_elf_ro {sec : Nat} {ds : List Directive} {k : Nat}
    (hk : ds.IsInfixAt (ElfHost.sectionProg sec) k)
    {S S' : SState} {x : Exit} (hx : exec ds S = some (S', x)) (hwf : env.WFRo)
    (hret : ∀ l, x = .call l → env.ret = (ElfHost.addrOf sec (k + ds.length)).toBitVec)
    {m : MachineData} (hm : Match env S m) :
    Eventually (elfStep1 ElfHost.exe) (fun st => Match env S' st.data ∧
      PcOk env x (ElfHost.addrOf sec (k + ds.length)) st) ⟨m, ElfHost.addrOf sec k⟩ := by
  induction ds generalizing k S m with
  | nil =>
    cases hx
    exact Eventually.done _ ⟨hm, rfl⟩
  | cons d ds ih =>
    have hd' := hk.cons
    cases hd : stepD d S with
    | none => simp [exec, hd] at hx
    | some r =>
      obtain ⟨S₁, x₁⟩ := r
      cases x₁ with
      | fall =>
        simp only [exec, hd] at hx
        have hlen : k + 1 + ds.length = k + (d :: ds).length := by
          simp [Nat.add_assoc, Nat.add_comm 1]
        refine eventually_trans _ _ _ _ (stepD_ok_elf_ro hk hwf hm hd nofun) fun st ⟨hm₁, hpc⟩ => ?_
        obtain ⟨m₁, pc⟩ := st
        simp only [PcOk] at hpc
        subst hpc
        have := ih hd'.2 hx (by rw [hlen]; exact hret) hm₁
        rwa [hlen] at this
      | _ =>
        cases ds with
        | cons _ _ => simp [exec, hd] at hx
        | nil =>
          simp only [exec, hd, Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          exact stepD_ok_elf_ro hk hwf hm hd hret

/-- **The symbolic executor is sound under a multi-section `ElfHost`.** -/
theorem exec_sound_elf {sec : Nat} {ds : List Directive} {k : Nat}
    (hk : ds.IsInfixAt (ElfHost.sectionProg sec) k)
    {S S' : SState} {x : Exit} (hx : exec ds S = some (S', x)) (hwf : env.WF)
    (hret : ∀ l, x = .call l → env.ret = (ElfHost.addrOf sec (k + ds.length)).toBitVec)
    {m : MachineData} (hm : Match env S m) :
    Eventually (elfStep1 ElfHost.exe) (fun st => Match env S' st.data ∧
      PcOk env x (ElfHost.addrOf sec (k + ds.length)) st) ⟨m, ElfHost.addrOf sec k⟩ :=
  exec_sound_elf_ro hk hx hwf.toWFRo hret hm

end

/-! ## The initial state -/

theorem allRegs_map_getElem? (f : Reg64 → Option Sym) (r : Reg64) :
    (allRegs.map f)[r.idx]? = some (f r) := by
  rw [List.getElem?_map, allRegs_idx]
  rfl

/-- The symbolic state `init` describes a machine state whose registers not in `known` are their
atoms, whose registers in `known` are their given values, whose flags are the environment's, whose
memory is the environment's, with regions of the sizes `regions` gives, where the bounds and
aliases hold. -/
theorem match_init [Labels] {env : Env} {regions : List Nat} {known : List (Reg64 × Sym)}
    {labels : List (Label × Nat)} {bounds : List (Sym × Nat)} {aliases : List (Sym × Nat × Int)}
    {m : MachineData}
    (hregs : ∀ r, known.lookup r = none → m.regs.get64 r = env.regs r)
    (hknown : ∀ r v, known.lookup r = some v → m.regs.get64 r = v.eval env)
    (hflags : m.status = env.flags)
    (hregions : ∀ (r n : Nat), regions[r]? = some n →
      ∃ b : BitVec 64, env.regions[r]? = some (b, n))
    (hlabels : ∀ l r, labels.lookup l = some r → env.base r = (Labels.label l).toBitVec)
    (hbounds : ∀ x n, (x, n) ∈ bounds → (x.eval env).toNat < n)
    (haliases : ∀ x r o, aliases.lookup x = some (r, o) →
      x.eval env = env.base r + BitVec.ofInt 64 o)
    (hmem : m.dmem = env.mem0)
    (hro : env.roRegions = [] := by rfl) :
    Match env (init regions known labels bounds aliases) m where
  regs r v h := by
    unfold SState.reg init at h
    rw [allRegs_map_getElem?] at h
    cases hl : known.lookup r with
    | none =>
      rw [hl] at h
      cases h
      exact hregs r hl
    | some u =>
      rw [hl] at h
      cases h
      exact hknown r u hl
  flags := by
    refine ⟨fun b h => ?_, fun b h => ?_, fun b h => ?_, fun b h => ?_⟩ <;> cases h <;>
      rw [hflags] <;> rfl
  regions := hregions
  mem r b n _ i _ := by
    rw [hmem]
    rfl
  labels := hlabels
  bounds := hbounds
  aliases := haliases
  outside a _ := by rw [hmem]
  known := by intro w h; cases h
  roRegions := hro.symm

end

end NativeRustcX64.Sym
