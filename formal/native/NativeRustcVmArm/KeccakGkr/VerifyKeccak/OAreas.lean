module

public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.TDefs

/-!
# `verify_keccak`: the openings' footprints

`keccak_open`'s `Areas` at the two openings: the output's `Option<EW>` in the frame (at 2592,
then 3240), the `TState`, the slot point at 2496, the scratch's `rows`; read: the decoded area, the
claim's point in the frame (at 480, then 1248), its bit weights in the scratch (`first_weights`,
then `weights`), the round constants, the stack arguments at SP.
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript

public section

variable [Labels] {a : DecArea} {s : TState} {cs : Array ColumnClaimW} {inst output : Array EW}
  {m0 st : MachineData}

omit [Labels] in
theorem ko_stack : keccakOpenStack = 3104 := rfl

/-- **An opening's footprint.** -/
theorem open_areas (h : P0 a s cs inst output m0) (hn : Nums a inst m0) (hfr : VFr m0 st)
    {o p w n : Nat} {wA : BitVec 64} (ho1 : 2592 ≤ o) (ho2 : o ≤ 3240) (hpn : p + 16 * n ≤ 2496)
    (hw : w ≤ 25600) (hwA : wA = scA m0 + BitVec.ofNat 64 w) :
    Areas st keccakOpenStack
      [⟨loc m0 o, 24⟩, ⟨tA m0, tstateBytes⟩, ⟨loc m0 2496, 96⟩,
        ⟨scA m0 + BitVec.ofNat 64 140288, NativeRustcVm.KeccakGkr.rowsBytes⟩]
      [a.region, ⟨loc m0 p, 16 * n⟩, ⟨wA, 25600⟩, rcRegion, ⟨loc m0 0, 32⟩] := by
  subst hwA
  have hN := hn.hN
  have hSP := m0.regs.SP.toNat_lt
  have hs : (stackBelow st 3104).toNat = m0.regs.SP.toNat - 3360 - 3104 :=
    sb_toNat hn.hN hfr (by decide)
  have hk := ko_stack
  have hw' : (scA m0 + BitVec.ofNat 64 w).toNat = (scA m0).toNat + w := scN hn (by omega)
  have hr : (scA m0 + BitVec.ofNat 64 140288).toNat = (scA m0).toNat + 140288 := scN hn (by omega)
  have lo := loc_toNat (m0 := m0) hn.hN (o := o) (by omega)
  have lp := loc_toNat (m0 := m0) hn.hN (o := p) (by omega)
  have l0 := loc_toNat (m0 := m0) hn.hN (o := 0) (by omega)
  have l2 := loc_toNat (m0 := m0) hn.hN (o := 2496) (by omega)
  have et : tstateBytes = 760 := rfl
  have er : NativeRustcVm.KeccakGkr.rowsBytes = 65536 := rfl
  areas_split
  · exact (ok_loc hn hfr (by omega)).1
  · exact (ok_loc hn hfr (by omega)).2
  · exact (ok_of (ok_t h) hn.tW hfr (by decide)).1
  · exact (ok_of (ok_t h) hn.tW hfr (by decide)).2
  · exact (ok_loc hn hfr (by omega)).1
  · exact (ok_loc hn hfr (by omega)).2
  · exact (ok_off (ok_sc h) hn.sW hfr (by decide) (by decide)).1
  · exact (ok_off (ok_sc h) hn.sW hfr (by decide) (by decide)).2
  · exact (ok_of (ok_w h) hn.wW hfr le_rfl).1
  · exact (ok_of (ok_w h) hn.wW hfr le_rfl).2
  · exact (ok_loc hn hfr (by omega)).1
  · exact (ok_loc hn hfr (by omega)).2
  · exact (ok_off (ok_sc h) hn.sW hfr (by decide) (by omega)).1
  · exact (ok_off (ok_sc h) hn.sW hfr (by decide) (by omega)).2
  · exact (ok_of (ok_rc h) hn.rcW hfr le_rfl).1
  · exact (ok_of (ok_rc h) hn.rcW hfr le_rfl).2
  · exact (ok_loc hn hfr (by omega)).1
  · exact (ok_loc hn hfr (by omega)).2
  all_goals simp only [NativeRustcArm.Apart, stackRegion,
    DecArea.region, rcRegion]
  all_goals try rw [hk]
  all_goals simp only [lo, lp, l0, l2, hr, hw', hs, et, er]
  all_goals clear lo lp l0 l2 hr hw' hs et er hk hfr h hSP
  all_goals first
    | omega
    | (obtain h1 | h1 := hn.tS <;> omega)
    | (obtain h1 | h1 := hn.sS <;> omega)
    | (obtain h1 | h1 := hn.txs <;> omega)
    | (obtain h1 | h1 := hn.wS <;> omega)
    | (obtain h1 | h1 := hn.rcS <;> omega)
    | (obtain h1 | h1 := hn.t_w <;> omega)
    | (obtain h1 | h1 := hn.t_rc <;> omega)
    | (obtain h1 | h1 := hn.s_w <;> omega)
    | (obtain h1 | h1 := hn.s_rc <;> omega)

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
