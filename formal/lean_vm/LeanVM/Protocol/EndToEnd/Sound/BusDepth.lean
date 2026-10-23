/-
  LeanVM.Protocol.EndToEnd.Sound.BusDepth

  The leanISA instance's bus depth, degree bound and constraint count, at the verifier's layout:
  the size facts the bus and table phases' specifications take as hypotheses.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.BusLayout
public import LeanVM.Protocol.EndToEnd.Front.LayoutStack

/-!
# The bus depth and the table sumcheck's sizes of the leanISA instance

The bus and table phases' specification (`Front.busTableSpec`) is stated over an abstract
instance and a verifier layout, and asks four size facts of them. For the leanISA instance
`leanIsaInstance F prog s` at the verifier's layout `verifierLayout prog s`, with any Flock
specification and at every size:

* `busLayout_depth_leanIsa`: the push side's depth the verifier computes (`busLayout`, the
  framework blocks `[0, log_mem, log_bytecode]` and the tables' push flushes) is the instance's
  `μBus`. The verifier's blocks are the instance's push boundary blocks (the state, memory and
  bytecode seeds, of log-heights `0`, `log_mem` and the program's) and push flushes (the Python
  tables' push flushes are Clean's, `pyFlush_eval`, so each table pushes as often), so the stacked
  total is `pushLeaves`; `log2_ceil` is `Nat.clog 2` (`log2Ceil_eq_clog`).
* `μBus_leanIsa_ne_zero`: the depth is positive, the memory seed alone having two leaves.
* `d_leanIsa_le`: the degree bound is `2`.
* `B_leanIsa`: the sumcheck tables have two constraints, `JUMP`'s; hence `B_leanIsa_le`.

No hypothesis on the sizes is needed: the facts hold of the instance as built.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete

@[expose] public section

/-! ## The push side's leaves -/

/-- Each opcode table pushes as often in the verifier's tables as in the instance. -/
theorem length_pySide_push (t : Fin 6) :
    (pySide t .push).length =
      ((LeanIsa.flushes (opIdx t)).filter fun f ↦ decide (f.1 = Side.push)).length := by
  have h := congrArg List.length (pyFlush_eval t .push fun _ ↦ 0)
  simpa only [List.length_map] using h

/-- The instance's push leaves: the three seeds' (state, memory, bytecode), then each opcode
table's push flushes. -/
theorem pushLeaves_leanIsa (F : FlockSpec) (prog : Program) (s : Sizes) :
    (leanIsaInstance F prog s).pushLeaves = (1 + 2 ^ s.logMem + 2 ^ prog.logSize) +
      ∑ t : Fin 6, ((LeanIsa.flushes (opIdx t)).filter fun f ↦ decide (f.1 = Side.push)).length *
        2 ^ s.τ t := by
  rw [M3Instance.pushLeaves, ← List.ofFn_eq_map, List.sum_ofFn]
  congr 1
  · show (((boundary prog s).filter fun b ↦ decide (b.side = .push)).map fun b ↦ 2 ^ b.κ).sum = _
    simp only [boundary, List.filter_cons, List.filter_nil, decide_true, decide_false,
      reduceCtorEq, ite_true, ite_false, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      pow_zero]
    omega
  · show ∑ j : Fin 9, ((LeanIsa.flushes j).filter fun f ↦ decide (f.1 = Side.push)).length *
        2 ^ height prog s j = _
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    have h0 : LeanIsa.flushes (0 : Fin 9) = [] := rfl
    have h1 : LeanIsa.flushes (Fin.succ 0 : Fin 9) = [] := rfl
    have h2 : LeanIsa.flushes ((Fin.succ 0).succ : Fin 9) = [] := rfl
    simp only [h0, h1, h2, List.filter_nil, List.length_nil, zero_mul, zero_add]
    rfl

/-- The push side's stacked total at the verifier's layout is the instance's push leaves. -/
theorem blockTotal_push_eq_pushLeaves (F : FlockSpec) (prog : Program) (s : Sizes) :
    blockTotal (sideSizes (fwLogs prog s) (pushBlocks s)) =
      (leanIsaInstance F prog s).pushLeaves := by
  rw [pushLeaves_leanIsa, blockTotal_sideSizes, pushBlocks, sum_flatten_ofFn, fwLogs]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_zero, List.map_map,
    Function.comp_def, List.map_const', List.sum_replicate, smul_eq_mul, length_pySide_push]
  omega

/-! ## The four facts -/

/-- The push side's depth at the verifier's layout is the instance's bus depth. -/
theorem busLayout_depth_leanIsa (F : FlockSpec) (prog : Program) (s : Sizes) :
    (busLayout [0, (verifierLayout prog s).logMemory, (verifierLayout prog s).logBytecode]
      (verifierLayout prog s).push).depth = (leanIsaInstance F prog s).μBus := by
  rw [busLayout_depth_verifier, busDepth, log2Ceil_eq_clog, blockTotal_push_eq_pushLeaves F]
  rfl

/-- The instance has at least two push leaves: the memory seed's. -/
theorem two_le_pushLeaves_leanIsa (F : FlockSpec) (prog : Program) (s : Sizes) :
    2 ≤ (leanIsaInstance F prog s).pushLeaves := by
  rw [pushLeaves_leanIsa]
  exact le_add_right (le_add_right (le_add_left (Nat.le_self_pow s.logMem_pos.ne' 2)))

/-- The instance's bus depth is positive. -/
theorem μBus_leanIsa_ne_zero (F : FlockSpec) (prog : Program) (s : Sizes) :
    (leanIsaInstance F prog s).μBus ≠ 0 :=
  (Nat.clog_pos (by norm_num) (two_le_pushLeaves_leanIsa F prog s)).ne'

/-- The instance's degree bound is `2`. -/
theorem d_leanIsa_le (F : FlockSpec) (prog : Program) (s : Sizes) :
    (leanIsaInstance F prog s).d ≤ 2 :=
  le_rfl

/-- The instance's constraint counts: `JUMP` (table `7`) has two, the others none. -/
theorem length_constraints : ∀ j : Fin 9,
    (LeanIsa.constraints j).length = if j = opIdx 4 then 2 else 0 := by
  decide +kernel

/-- The sumcheck tables have two constraints, `JUMP`'s. -/
theorem B_leanIsa (F : FlockSpec) (prog : Program) (s : Sizes) :
    (leanIsaInstance F prog s).B = 2 := by
  let I := leanIsaInstance F prog s
  have hsub : I.B = ∑ j ∈ Finset.univ.filter I.SumcheckTable, (I.constraints j).length :=
    (Finset.sum_subtype _ (by simp) (fun j ↦ (I.constraints j).length)).symm
  have hfil : ∑ j ∈ Finset.univ.filter I.SumcheckTable, (I.constraints j).length =
      ∑ j : Fin 9, (LeanIsa.constraints j).length :=
    Finset.sum_filter_of_ne fun _ _ hj ↦
      Or.inl (List.ne_nil_of_length_pos (Nat.pos_of_ne_zero hj))
  rw [show (leanIsaInstance F prog s).B = I.B from rfl, hsub, hfil,
    Finset.sum_congr rfl fun j _ ↦ length_constraints j, Finset.sum_ite_eq']
  simp

/-- The instance's constraint count is at most `2 ^ 20`. -/
theorem B_leanIsa_le (F : FlockSpec) (prog : Program) (s : Sizes) :
    (leanIsaInstance F prog s).B ≤ 2 ^ 20 := by
  rw [B_leanIsa]
  norm_num

end
end LeanVM.Protocol.EndToEnd.Sound
