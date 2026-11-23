module

public import NativeRustcVmArm.Tables.TableTerms.Blocks

/-!
# `table_terms`: the entry

`b0` saves the registers, stores the arguments in the frame (`out`, the powers, the point, the
`TState`, the weights' address plus `8`, the heights'), points X19, X21 at `TABLES`' first width,
zeroes the sum and the cursor, and falls into the loop head with no table done (`Head 0`).
Region 0 the frame and the two stack arguments above it (`envA`).
-/

namespace NativeRustcVmArm.Tables.TableTerms

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVmArm.Vm.TableTerms
open NativeRustcVm (wordOf ewsOf)
open NativeRustcVmArm.Bus (after)

@[expose] public section

/-- The entry's environment: the frame and the stack arguments. -/
abbrev envA (m0 : MachineData) : Env := Env.ofMachine m0 [(base m0 288, 304)]

end

public section

variable [Labels] {a : DecArea} {s : TState} {heights : Array Nat} {forms : Array (Array FormW)}
  {m0 : MachineData}

theorem envA_wf (h : TableTermsPre a s heights forms m0) : (envA m0).WF := by
  have hS := Pre.stack h
  have hN := hS.2.1
  have hspb : base m0 288 + BitVec.ofNat 64 288 = m0.regs.SP.toBitVec := base_add_eq
  have hbase : (base m0 288).toNat = m0.regs.SP.toNat - 288 :=
    base_toNat (by rw [N_eq] at hN; omega)
  have hargs := Pre.args h
  refine Env.wf_of ⟨⟨fun i hi ↦ ?_, ?_⟩, trivial⟩ (List.pairwise_singleton _ _)
  · by_cases hi' : i < 288
    · exact (Bus.frame_mapped hS (by rw [N_eq]; omega)).1 i hi'
    · have := hargs.1 (i - 288) (by omega)
      rwa [← hspb, NativeRustcVm.addr_add_add, show 288 + (i - 288) = i by omega] at this
  · have := hargs.2
    unfold NoWrap at this ⊢
    rw [hbase]
    have : m0.regs.SP.toBitVec.toNat = m0.regs.SP.toNat := rfl
    rw [N_eq] at hN
    omega

theorem envA_match (h : TableTermsPre a s heights forms m0) : Match (envA m0) entryS m0 :=
  match_ofMachine (sregions := [(304, true)]) (regions := [(base m0 288, 304)])
    ⟨rfl, fun _ ↦ Bus.base_aligned (Pre.stack h) (by rw [N_eq]; omega) rfl, trivial⟩
    (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]
        rw [show BitVec.ofInt 64 288 = BitVec.ofNat 64 288 from rfl]; exact base_add_eq.symm)
    trivial trivial trivial trivial

/-- A stack argument as the entry's environment loads it. -/
theorem ldA (o : Nat) :
    (Sym.load 0 (288 + o) 8).eval (envA m0) = stackWord m0 o := by
  show Env.load _ 0 (288 + o) 8 = _
  rw [load_eq_wordOf]
  simp only [Env.ofMachine_mem0, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
    Option.getD_some, stackWord]
  rw [← NativeRustcVm.addr_add_add, base_add_eq]

end

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {heights : Array Nat}
  {forms : Array (Array FormW)} {m0 : MachineData}

/-- **The entry**: the loop head before table `0`. -/
theorem entry (hp : Placed code k) (h : TableTermsPre a s heights forms m0)
    {R : MachineState → Prop}
    (cont : ∀ m, Head a s heights forms m0 0 (0, 0, #[]) s m →
      Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b1Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b0Offset)⟩ := by
  have hS := Pre.stack h
  have hN := spN h
  have hwf := envA_wf h
  refine exec_then (hb0 hp) run_b0 hwf (envA_match h) fun st hm hpc ↦ ?_
  have hm' : Match (envA m0) (after b0 entryS) st.data := by rw [Bus.after_eq run_b0]; exact hm
  obtain ⟨hsp, hok, hmem, l16, l24, l32, l40, l48, l56, l96, l104, r19, r21, r20, r22, r23, r26,
    r27, r29⟩ := ok_b0
  have hfrF : Fr m0 288 N slots [] (fun _ ↦ False) st.data :=
    Bus.Fr.ofPrologue' (A := 16) hN (by rw [N_eq]; omega) hm' hwf hsp hok slots_le hmem
      (fun _ h ↦ nomatch h)
  have hfr : Fr m0 288 N slots [] (outs m0) st.data := Bus.Fr.mono hfrF fun _ h ↦ h.elim
  have W : ∀ {o : Nat} {v : Sym}, o + 8 ≤ 288 → loadSym (after b0 entryS).mem 0 o 8 = v →
      fw m0 st.data o = v.eval (envA m0) := fun {o v} hle hv ↦ by
    unfold fw
    rw [match_wordOf hm' hwf (r := 0) (b := base m0 288) (sz := 304) rfl (by omega), hv]
  have ev1 : ∀ {r : XReg} {v : Sym}, (after b0 entryS).reg r = some v →
      rg st.data r = v.eval (envA m0) := fun hr ↦ rv hm' hr
  simp only [PcOk] at hpc
  refine Bus.Gkr.at_pc (hpc.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TableTerms.b0_next]))) (cont st.data ?_)
  have hT : (Sym.bin .add .W64 (.label tablesL) (.lit 8)).eval (envA m0) =
      T + BitVec.ofNat 64 (8 + 40 * 0) := by
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]; rfl
  refine ⟨hfr, ?_, (ev1 r19).trans hT, (ev1 r21).trans hT, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl,
    ts_keep h (i := 0) (by decide) hfrF.kept hfrF.same
      (fun q hq ↦ hq.elim (fun hs ↦ .inl hs) False.elim) (Pre.ts h), fun j hj ↦ by cases hj⟩
  · intro p hp
    simp only [cws, lws, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact W (by omega) l16
    · exact W (by omega) l24
    · exact W (by omega) l32
    · exact W (by omega) l40
    · exact W (by omega) l48
    · exact W (by omega) l56
    · rw [W (by omega) l96, show (Sym.bin .add .W64 (.load 0 288 8) (.lit 8)).eval (envA m0) =
          (Sym.load 0 (288 + 0) 8).eval (envA m0) + BitVec.ofNat 64 8 by
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64], ldA]
      rfl
    · rw [W (by omega) l104]
      simp only [Sym.eval, Env.ofMachine_regs]
      exact (BitVec.add_zero _).symm
  · rw [ev1 r20]; exact (BitVec.add_zero _).symm
  · rw [ev1 r27, show (296 : Nat) = 288 + 8 from rfl, ldA]
    exact (BitVec.add_zero _).symm
  · rw [ev1 r29]; rfl
  · rw [ev1 r26]; rfl
  · exact UInt64.toBitVec_inj.mp ((ev1 r22).trans rfl)
  · exact UInt64.toBitVec_inj.mp ((ev1 r23).trans rfl)

end

end NativeRustcVmArm.Tables.TableTerms
