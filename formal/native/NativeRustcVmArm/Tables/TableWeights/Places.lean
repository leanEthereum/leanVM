module

public import NativeRustcVmArm.Tables.TableWeights.Glue

/-!
# `table_weights`: places through a block

A place's start symbol is its value (`Pl.sym_eval`); after a block and a call of `EW::mul` a
place is the value of its symbolic value (`Pl.val_after`); a weight passed to `EW::mul` from its
places (`weight_of`). A state with the frame's invariant gives the environment of the frame and
the read-only regions `rs` (`match_frame`), and the frame for `EW::mul` (`Frm.frameOk`).
-/

namespace NativeRustcVmArm.Tables.TableWeights

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Tables
open NativeRustcVm (wordOf)

@[expose] public section

/-- A place a block and a call keep track of: a callee-saved register or a frame word. -/
def Pl.Ok : Pl → Prop
  | .reg r => calleeSaved r = true
  | .slot o => o + 8 ≤ 240

instance : (p : Pl) → Decidable p.Ok
  | .reg r => inferInstanceAs (Decidable (calleeSaved r = true))
  | .slot o => inferInstanceAs (Decidable (o + 8 ≤ 240))

end

public section

variable {m0 : MachineData}

theorem lo_ok {j : Nat} : (lo j).Ok := by
  rcases j with _ | _ | _ | _ | _ | j <;> simp [lo, Pl.Ok, calleeSaved]

theorem hi_ok {j : Nat} : (hi j).Ok := by
  rcases j with _ | _ | _ | _ | _ | j <;> simp [hi, Pl.Ok]

theorem hoff_mem {j : Nat} (hj : j < 6) : (hoff j, hword m0 j) ∈ kslots m0 := by
  rcases j with _ | _ | _ | _ | _ | _ | j <;> simp [kslots, hoff]; omega

variable [Labels]

theorem Pl.sym_eval (m : MachineData) (rs : List (BitVec 64 × Nat)) (p : Pl) :
    p.sym.eval (Env.ofMachine m ((fb m0, 240) :: rs)) = p.val m0 m := by
  cases p with
  | reg r => rfl
  | slot o => exact load_fw m rs o

/-- **A place after a block and a call.** -/
theorem Pl.val_after {st : MachineData} {S' : SState} {env : Env}
    (hsv : ∀ r v, calleeSaved r = true → S'.reg r = some v →
      (st.regs.getXReg r).toBitVec = v.eval env)
    (hwd : ∀ o, o + 8 ≤ 240 → (wordOf st.dmem (fb m0 + BitVec.ofNat 64 o)).toBitVec =
      (loadSym S'.mem 0 o 8).eval env)
    {p : Pl} (hp : p.Ok) {v : Sym} (h : p.after S' = some v) : p.val m0 st = v.eval env := by
  cases p with
  | reg r => exact hsv r v hp h
  | slot o =>
    simp only [Pl.after, Option.some.injEq] at h
    rw [Pl.val, fw, hwd o hp, h]

/-- A weight passed to `EW::mul` from its places. -/
theorem weight_of {m : MachineData} {rs : List (BitVec 64 × Nat)} {j : Nat} {w : EW}
    (h : WAt m0 m j w) :
    (⟨.ofBitVec ((lo j).sym.eval (Env.ofMachine m ((fb m0, 240) :: rs))),
      .ofBitVec ((hi j).sym.eval (Env.ofMachine m ((fb m0, 240) :: rs)))⟩ : EW) = w := by
  rw [Pl.sym_eval, Pl.sym_eval, h.1, h.2]

omit [Labels] in
/-- The frame for `EW::mul` in a state of the body. -/
theorem Frm.frameOk {m : MachineData} (hg : Geo m0) (hf : Frm m0 m) :
    FrameOk m.dmem (fb m0) 240 :=
  ⟨hg.al, hg.lo, hg.hi, fun i hi => hf.kept _ (hg.map i hi)⟩

/-- **The environment of a state of the body**: the frame, region 0, and the regions `rs`. -/
theorem match_frame {m : MachineData} (hg : Geo m0) (hf : Frm m0 m)
    {rs : List (BitVec 64 × Nat)} {srs : List (Nat × Bool)} (hrs : RegionsOk srs rs)
    {known : List (XReg × Sym)} (hknown : AllOf (fun p =>
      (m.regs.getXReg p.1).toBitVec = p.2.eval (Env.ofMachine m ((fb m0, 240) :: rs))) known)
    {aliases : List (Sym × Nat × Int)} (haliases : AllOf (fun p =>
      p.1.eval (Env.ofMachine m ((fb m0, 240) :: rs)) =
        (Env.ofMachine m ((fb m0, 240) :: rs)).base p.2.1 + BitVec.ofInt 64 p.2.2) aliases) :
    Match (Env.ofMachine m ((fb m0, 240) :: rs))
      (init ((240, true) :: srs) (.ptr 0 0) known [] [] aliases) m :=
  match_ofMachine ⟨rfl, fun _ => hg.al, hrs⟩
    (by rw [hf.sp]; simp [Sym.eval]) hknown trivial trivial haliases

end

end NativeRustcVmArm.Tables.TableWeights
