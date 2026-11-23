module

public import NativeRustcVmArm.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Open1

/-!
# `verify_keccak`: the committed outputs' word

`b42`: the first opening's value into X29, X19, `read_scalar` into the frame's `Option<EW>` at
2592; `b43`: its tag. At `b44`: `AtR`. A transcript call's change as numbers (`TKeep.chg`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt)

public section

/-- A transcript call's change within `WS`. -/
theorem TKeep.chg {m0 : MachineData} {o n : Nat} {d d' : Mem 64} (h : TKeep m0 o n d d') :
    Chg m0 [(o, o + n)] [(0, 0, 760)] d d' := by
  intro q hq
  refine h q fun h1 ↦ hq ?_
  rcases h1 with h1 | h1 | h1
  · exact .inr (.inl ⟨_, List.mem_singleton_self _, h1.1, by simp only; omega⟩)
  · exact .inr (.inr ⟨_, List.mem_singleton_self _, by simp only [ob]; omega,
      by simp only [ob]; omega⟩)
  · exact .inl h1

variable [Host] {k : Nat} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output : Array EW} {m0 : MachineData}

/-- **The committed outputs' word** (`b42`, `b43`). -/
theorem stepRead1 (hp : Placed code k) (h : P0 a s cs inst output m0) (hn : Nums a inst m0)
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    {m : MachineData} {s1 : TState} {cj : KeccakClaimW} {sl ws : Array EW} {v : EW}
    (ho : AtO a s cs inst output m0 m s1 cj sl ws v)
    (cont : ∀ m' s' w, AtR a s cs inst output m0 m' s' cj sl ws v w →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b44Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b42Offset)⟩ := by
  have ev := ho.val.2
  rw [show off (loc m0 2592) 8 = loc m0 2600 from loc_add m0 2592 8] at ev
  have ec := load_ew (env := envM m0 m) (r := 0) (o := 2600) ev
  refine rsStep h hn hrs (b42_in_code.trans hp.1 (by simp [b42])) run_b42 ho.mid ho.ts ho.cls
    rfl rfl (by decide) rfl rfl (o := 2592) (by decide) (by decide)
    fun st m2 hm1 hv hnx hmid2 hcl2 hk2 hcs2 ↦ ?_
  have T := hk2.chg
  have x29 : m2.regs.getXReg .X29 = v.c0 := by
    rw [hcs2 .X29 rfl]; exact reg_of hm1 (r := .X29) (v := .load 0 2600 8) rfl ec.1
  have x19 : m2.regs.getXReg .X19 = v.c1 := by
    rw [hcs2 .X19 rfl]; exact reg_of hm1 (r := .X19) (v := .load 0 2608 8) rfl ec.2
  have x28 : (m2.regs.getXReg .X28).toBitVec = scA m0 + BitVec.ofNat 64 139264 := by
    rw [hcs2 .X28 rfl, Match.reg_eq (matchM hn ho.mid.fr) hm1 (r := .X28) rfl rfl]; exact ho.x28
  rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b42Offset + b42.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b43Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b42_next]]
  refine failBranch hp hn (b43_in_code.trans hp.1 (by simp [b43])) run_b43 hmid2 rfl rfl
    (by decide) (by decide) (b := ((readScalar.run s1).map (·.1)).isSome)
    (cond4 (o := 2592) (r := (readScalar.run s1).map (·.1)) hv) (fun hf ↦ ?_)
    fun ht m3 hmid3 hd3 hcs3 ↦ ?_
  · cases hr : readScalar.run s1 with
    | none => rw [ho.run, afterOpen1_none hr]
    | some _ => rw [hr] at hf; cases hf
  · obtain ⟨⟨w, s2⟩, hr⟩ : ∃ q, readScalar.run s1 = some q := by
      cases hq : readScalar.run s1 with
      | none => rw [hq] at ht; cases ht
      | some q => exact ⟨q, rfl⟩
    rw [hr] at hv hnx
    rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b43Offset + b43.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b44Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b43_next]]
    refine cont m3 s2 w ⟨hmid3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ho.psz, ho.slsz, ?_,
      ho.wsz, ?_, ?_, ?_⟩
    · rw [hcs3 .X28 rfl]; exact x28
    · rw [hcs3 .X29 rfl]; exact x29
    · rw [hcs3 .X19 rfl]; exact x19
    · rw [hd3]; exact T.word hn (by decide) (by decide) (by decide) ho.w40
    · rw [hd3]; exact T.word hn (by decide) (by decide) (by decide) ho.w64
    · rw [hd3]; exact T.word hn (by decide) (by decide) (by decide) ho.w72
    · rw [hd3]; exact hnx w s2 rfl
    · rw [hd3]; exact hcl2
    · rw [hd3]; exact T.claim hn (by decide) (by decide) (by decide) ho.claim
    · rw [hd3]; exact T.wts hn (by decide) (by decide) (by decide) (by decide) ho.wts
    · rw [hd3]
      exact T.ews hn (by decide) (o := 2496) (k := 96) (by decide) (by decide)
        (by simp [Array.length_toList, ho.slsz]) ho.slot
    · rw [hd3]
      exact T.ewsOut hn (by decide) (by decide) (i := 1) (o := 140288) (k := 1024) (by decide)
        (by decide) (by decide) (by decide) (by simp [Array.length_toList, ho.wsz]) ho.rows
    · rw [hd3]; exact hv
    · rw [ho.run, afterOpen1_some hr]

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
