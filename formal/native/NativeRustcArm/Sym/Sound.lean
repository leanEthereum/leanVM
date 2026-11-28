module

public import NativeRustcArm.Sym.Sound.Data
public import NativeRustcArm.Sym.Sound.Mem
public import NativeRustcArm.Sym.Sound.Branch

/-!
# The symbolic executor is sound

`Sym.exec_sound`: where the symbolic executor runs a block `ds` placed at directive `k` of the
program from a symbolic state `S` to `S'` with exit `x`, the machine, from any state `S`
describes at the block's address, inevitably reaches a state `S'` describes, at the pc `x` says
(`PcOk`, with the address after the block for a fall-through or an untaken branch).
`Sym.match_init`: the initial symbolic state of a machine state describes it.
-/

namespace NativeRustcArm.Sym

open NativeRustcArm

public section

/-- Every instruction is sound. -/
theorem stepOp_ok [Labels] {env : Env} {w : RegWidth} (op : Operation w) : OpOk env op := by
  cases op with
  | LDR dst src =>
    cases src with
    | addr ae => exact ok_LDR dst ae
    | lit _ => intro _ _ _ _ _ _ _ h; cases h
  | STR src ae => exact ok_STR src ae
  | LDUR dst ua => exact ok_LDUR dst ua
  | STUR src ua => exact ok_STUR src ua
  | LDP dst1 dst2 ae => exact ok_LDP dst1 dst2 ae
  | STP src1 src2 ae => exact ok_STP src1 src2 ae
  | LDRB dst ae => exact ok_LDRB dst ae
  | LDURB dst ua => exact ok_LDURB dst ua
  | STRB src ae => exact ok_STRB src ae
  | STURB src ua => exact ok_STURB src ua
  | LDRH dst ae => exact ok_LDRH dst ae
  | LDURH dst ua => exact ok_LDURH dst ua
  | STRH src ae => exact ok_STRH src ae
  | STURH src ua => exact ok_STURH src ua
  | ADD_e dst src1 src2 => exact ok_ADD_e dst src1 src2
  | ADD_s dst src1 src2 => exact ok_ADD_s dst src1 src2
  | ADDS_e dst src1 src2 => exact ok_ADDS_e dst src1 src2
  | ADDS_s dst src1 src2 => exact ok_ADDS_s dst src1 src2
  | SUB_e dst src1 src2 => exact ok_SUB_e dst src1 src2
  | SUB_s dst src1 src2 => exact ok_SUB_s dst src1 src2
  | SUBS_e dst src1 src2 => exact ok_SUBS_e dst src1 src2
  | SUBS_s dst src1 src2 => exact ok_SUBS_s dst src1 src2
  | MADD dst src1 src2 src3 => exact ok_MADD dst src1 src2 src3
  | MSUB dst src1 src2 src3 => exact ok_MSUB dst src1 src2 src3
  | UMULH dst src1 src2 => exact ok_UMULH dst src1 src2
  | UMADDL dst src1 src2 src3 => exact ok_UMADDL dst src1 src2 src3
  | AND_i dst src1 imm => exact ok_AND_i dst src1 imm
  | AND_s dst src1 src2 => exact ok_AND_s dst src1 src2
  | ANDS_i dst src1 imm => exact ok_ANDS_i dst src1 imm
  | ANDS_s dst src1 src2 => exact ok_ANDS_s dst src1 src2
  | ORR_i dst src1 imm => exact ok_ORR_i dst src1 imm
  | ORR_s dst src1 src2 => exact ok_ORR_s dst src1 src2
  | ORN_s dst src1 src2 => exact ok_ORN_s dst src1 src2
  | EOR_i dst src1 imm => exact ok_EOR_i dst src1 imm
  | EOR_s dst src1 src2 => exact ok_EOR_s dst src1 src2
  | EON_s dst src1 src2 => exact ok_EON_s dst src1 src2
  | BIC_s dst src1 src2 => exact ok_BIC_s dst src1 src2
  | BICS_s dst src1 src2 => exact ok_BICS_s dst src1 src2
  | BFM dst src immr imms => exact ok_BFM dst src immr imms
  | SBFM dst src immr imms => exact ok_SBFM dst src immr imms
  | UBFM dst src immr imms => exact ok_UBFM dst src immr imms
  | REV dst src => exact ok_REV dst src
  | RBIT dst src => exact ok_RBIT dst src
  | EXTR dst src1 src2 lsb => exact ok_EXTR dst src1 src2 lsb
  | MOVZ dst imm sh => exact ok_MOVZ dst imm sh
  | MOVK dst imm sh => exact ok_MOVK dst imm sh
  | MOVN dst imm sh => exact ok_MOVN dst imm sh
  | LSLV dst src1 src2 => exact ok_LSLV dst src1 src2
  | LSRV dst src1 src2 => exact ok_LSRV dst src1 src2
  | ASRV dst src1 src2 => exact ok_ASRV dst src1 src2
  | RORV dst src1 src2 => exact ok_RORV dst src1 src2
  | CSEL dst src1 src2 cond => exact ok_CSEL dst src1 src2 cond
  | CSINC dst src1 src2 cond => exact ok_CSINC dst src1 src2 cond
  | CSINV dst src1 src2 cond => exact ok_CSINV dst src1 src2 cond
  | CSNEG dst src1 src2 cond => exact ok_CSNEG dst src1 src2 cond
  | CCMP_reg src1 src2 nzcv cond => exact ok_CCMP_reg src1 src2 nzcv cond
  | CCMP_imm src1 imm nzcv cond => exact ok_CCMP_imm src1 imm nzcv cond
  | CCMN_reg src1 src2 nzcv cond => exact ok_CCMN_reg src1 src2 nzcv cond
  | CCMN_imm src1 imm nzcv cond => exact ok_CCMN_imm src1 imm nzcv cond
  | ADRP dst t => exact ok_ADRP dst t
  | B t => exact ok_B t
  | B_cond cond t => exact ok_B_cond cond t
  | BL t => exact ok_BL t
  | RET r => exact ok_RET r
  | CBZ r t => exact ok_CBZ r t
  | CBNZ r t => exact ok_CBNZ r t
  | TBZ r bit t => exact ok_TBZ r bit t
  | TBNZ r bit t => exact ok_TBNZ r bit t
  | NOP => exact ok_NOP
  | _ => intro _ _ _ _ _ _ _ h; cases h

section
variable [Host] {env : Env}

/-- One directive of a block: a label falls through, an instruction is sound. -/
theorem stepD_ok {d : Directive} {p : Program} {k : Nat} (hdp : (d :: p).IsInfixAt Host.prog k)
    {S S' : SState} {x : Exit} {m : MachineData} (hwf : env.WF) (hm : Match env S m)
    (h : stepD d S = some (S', x)) :
    Eventually (step1 Host.exe) (fun st => Match env S' st.data ∧
      PcOk env x (Host.addrOf k.succ) st) ⟨m, Host.addrOf k⟩ := by
  apply Host.eventually_of_interp hdp
  cases d with
  | label l =>
    cases h
    exact done_fall (p := ⟨Host.addrOf k, Host.addrOf k.succ⟩) hm
  | instr i =>
    exact stepOp_ok i.operation S S' x m ⟨Host.addrOf k, Host.addrOf k.succ⟩ hwf hm h
  | byteArray _ => cases h
  | word _ _ => cases h

/-- **The symbolic executor is sound.** Where it runs the block `ds`, placed at directive `k`
of the program, from `S` to `S'` with exit `x`, the machine inevitably goes from any state `S`
describes at the block's address to a state `S'` describes, at the pc `x` says. -/
theorem exec_sound {ds : List Directive} {k : Nat} (hk : ds.IsInfixAt Host.prog k)
    {S S' : SState} {x : Exit} (hx : exec ds S = some (S', x)) (hwf : env.WF)
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
        refine eventually_trans _ _ _ _ (stepD_ok hk hwf hm hd) fun st ⟨hm₁, hpc⟩ => ?_
        obtain ⟨m₁, pc⟩ := st
        simp only [PcOk] at hpc
        subst hpc
        have := ih hd'.2 hx hm₁
        rwa [show k + 1 + ds.length = k + (d :: ds).length by simp [Nat.add_assoc, Nat.add_comm 1]]
          at this
      | _ =>
        cases ds with
        | cons _ _ => simp [exec, hd] at hx
        | nil =>
          simp only [exec, hd, Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          exact stepD_ok hk hwf hm hd

end

/-! ## The initial state -/

theorem allXRegs_map_getElem? (f : XReg → Option Sym) (r : XReg) :
    (allXRegs.map f)[r.idx]? = some (f r) := by
  rw [List.getElem?_map, allXRegs_idx]
  rfl

/-- The symbolic state `init` describes a machine state whose registers not in `known` are their
atoms, whose registers in `known` are their given values, whose SP is `sp₀`, whose flags are the
environment's, whose memory is the environment's, with regions of the sizes and alignments
`regions` gives, the labels `labels` at their regions' bases and the bounds `bounds`. -/
theorem match_init [Labels] {env : Env} {regions : List (Nat × Bool)} {sp₀ : Sym}
    {known : List (XReg × Sym)} {labels : List (Label × Nat)} {bounds : List (Sym × Nat)}
    {aliases : List (Sym × Nat × Int)}
    {m : MachineData}
    (hregs : ∀ r, known.lookup r = none → (m.regs.getXReg r).toBitVec = env.regs r)
    (hknown : ∀ r v, known.lookup r = some v → (m.regs.getXReg r).toBitVec = v.eval env)
    (hsp : m.regs.SP.toBitVec = sp₀.eval env) (hflags : m.status = env.flags)
    (hregions : ∀ (r n : Nat) (al : Bool), regions[r]? = some (n, al) →
      ∃ b : BitVec 64, env.regions[r]? = some (b, n) ∧ (al = true → b.toNat % 16 = 0))
    (hlabels : ∀ l r, labels.lookup l = some r → env.base r = (Labels.label l).toBitVec)
    (hbounds : ∀ x n, (x, n) ∈ bounds → (x.eval env).toNat < n)
    (haliases : ∀ x r o, aliases.lookup x = some (r, o) → x.eval env = env.base r + BitVec.ofInt 64 o)
    (hmem : m.dmem = env.mem0) :
    Match env (init regions sp₀ known labels bounds aliases) m where
  regs r v h := by
    unfold SState.reg init at h
    rw [allXRegs_map_getElem?] at h
    cases hl : known.lookup r with
    | none =>
      rw [hl] at h
      cases h
      exact hregs r hl
    | some u =>
      rw [hl] at h
      cases h
      exact hknown r u hl
  sp := hsp
  flags f h := by
    cases h
    rw [hflags]
    rfl
  regions := hregions
  mem r b n _ i _ := by
    rw [hmem]
    rfl
  labels := hlabels
  bounds := hbounds
  aliases := haliases
  outside a _ := by rw [hmem]

end

end NativeRustcArm.Sym
