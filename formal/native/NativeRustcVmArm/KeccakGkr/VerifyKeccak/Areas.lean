module

public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Img

/-!
# A callee's footprint (`Areas`) from numbers

`areas_split` turns `Areas m n ws rs` for literal lists into its region facts (`Region.Ok`, by
`ok_loc`, `ok_of`) and its separations, each an `Apart` the caller proves by `omega` on addresses
as numbers.
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript
open NativeRustcVm (Region)

public section

variable [Labels] {a : DecArea} {inst : Array EW} {m0 st : MachineData}

theorem ok_loc (hn : Nums a inst m0) (hfr : VFr m0 st) {o n : Nat} (ho : o + n ≤ 3360) :
    Region.Ok st.dmem ⟨loc m0 o, n⟩ :=
  ⟨frame_mapped' hn hfr ho, loc_noWrap hn ho⟩

omit [Labels] in
theorem ok_of {A : BitVec 64} {N : Nat} (hm : Mapped m0.dmem A N) (hw : A.toNat + N ≤ 2 ^ 64)
    (hfr : VFr m0 st) {n : Nat} (hn : n ≤ N) : Region.Ok st.dmem ⟨A, n⟩ :=
  ⟨Mapped.kept' (fun i hi ↦ hm i (by simp only at hi; omega)) hfr.kept, by
    show A.toNat + n ≤ 2 ^ 64; omega⟩

omit [Labels] in
theorem disjoint_cons' {r : Region} {rs : List Region} :
    NativeRustcVm.Disjoint (r :: rs) ↔
      (∀ r' ∈ rs, Apart r.addr r.size r'.addr r'.size) ∧ NativeRustcVm.Disjoint rs :=
  List.pairwise_cons

omit [Labels] in
theorem disjoint_nil : NativeRustcVm.Disjoint [] := List.Pairwise.nil

end

/-- Splits `Areas m n ws rs` (literal lists) into its region facts and its separations. -/
macro "areas_split" : tactic => `(tactic| (
  refine ⟨?_, ?_, ?_⟩ <;>
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, NativeRustcVmArm.KeccakGkr.VerifyKeccak.disjoint_cons',
    NativeRustcVmArm.KeccakGkr.VerifyKeccak.disjoint_nil, and_true, true_and,
    imp_false, not_false_eq_true, false_implies, implies_true] <;>
  and_intros))

/-- An `Apart` of the frame's, the callee's stack's and the entry's regions, as numbers: by `omega`
with at most one of the entry's separations (`Nums`). -/
macro "apart_auto " hn:term:max hfr:term:max : tactic => `(tactic| (
  try unfold NativeRustcVm.Apart
  try unfold NativeRustcArm.Apart
  simp (disch := decide) only [NativeRustcVmArm.KeccakGkr.VerifyKeccak.sb_toNat ($hn).hN $hfr,
    NativeRustcVmArm.KeccakGkr.VerifyKeccak.loc_toNat ($hn).hN, NativeRustcVmArm.ewsRegion,
    NativeRustcVmArm.stackRegion, NativeRustcVm.Transcript.DecArea.region,
        NativeRustcVmArm.rcRegion,
    NativeRustcVmArm.projectRegion, NativeRustcVmArm.rhoRegion,
    NativeRustcVm.Transcript.tstateBytes, NativeRustcVm.Layout.claimsBytes,
    NativeRustcVm.KeccakGkr.scratchBytes, NativeRustcVm.KeccakGkr.outBytes,
    NativeRustcVm.KeccakGkr.claimBytes, NativeRustcVm.KeccakGkr.weightsBytes,
    NativeRustcVm.KeccakGkr.rowsBytes]
  have := ($hn).hN
  first
    | omega
    | (have := ($hn).tS; omega)
    | (have := ($hn).sS; omega)
    | (have := ($hn).cS; omega)
    | (have := ($hn).oS; omega)
    | (have := ($hn).wS; omega)
    | (have := ($hn).iS; omega)
    | (have := ($hn).pS; omega)
    | (have := ($hn).rcS; omega)
    | (have := ($hn).pjS; omega)
    | (have := ($hn).rhS; omega)
    | (have := ($hn).txs; omega)
    | (have := ($hn).txc; omega)
    | (have := ($hn).txo; omega)
    | (have := ($hn).sxc; omega)
    | (have := ($hn).sxo; omega)
    | (have := ($hn).cxo; omega)
    | (have := ($hn).t_w; omega)
    | (have := ($hn).t_i; omega)
    | (have := ($hn).t_p; omega)
    | (have := ($hn).t_rc; omega)
    | (have := ($hn).t_pj; omega)
    | (have := ($hn).t_rh; omega)
    | (have := ($hn).s_w; omega)
    | (have := ($hn).s_i; omega)
    | (have := ($hn).s_p; omega)
    | (have := ($hn).s_rc; omega)
    | (have := ($hn).s_pj; omega)
    | (have := ($hn).s_rh; omega)
    | (have := ($hn).c_w; omega)
    | (have := ($hn).c_i; omega)
    | (have := ($hn).c_p; omega)
    | (have := ($hn).c_rc; omega)
    | (have := ($hn).c_pj; omega)
    | (have := ($hn).c_rh; omega)
    | (have := ($hn).o_w; omega)
    | (have := ($hn).o_i; omega)
    | (have := ($hn).o_p; omega)
    | (have := ($hn).o_rc; omega)
    | (have := ($hn).o_pj; omega)
    | (have := ($hn).o_rh; omega)))

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
