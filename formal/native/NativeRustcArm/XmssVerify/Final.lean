module

public import NativeRustcArm.XmssVerify.TopLeaf
public import NativeRustcArm.XmssVerify.Epilogue

/-!
# `xmss_verify`: the comparison with the key's root, the layers composed

Block 25 (`final`): the top root in `x9`, `x8` compared with the key's root at `2448`, `1` in X0
if equal else `0`, then the epilogue. `layers`: from `Parsed` at block 5, the bottom layer, the top
layer and the comparison, or the rejection where a layer has no root; X0 is `xmssVerify`'s
result (`xmssVerify_eq`).
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustcArm.Sym NativeRustcArm LeanVM.Protocol.KeccakHash NativeRustc NativeRustc.Xmss

set_option Elab.async false

public section

variable [Host] {w : Nat → UInt64} {m₀ : MachineData}

omit [Host] in
/-- `cmp a, c; ccmp b, d, #0, eq; cset w0, eq`. -/
theorem eval_cmp2 [Labels] (env : Env) (a b c d : Sym) :
    (Sym.ite (.not (.ite (.cmp .eq .W64 a c) (.cmp .eq .W64 b d) (.lit false))) (.lit 0)
      (.lit 1)).eval env =
      (if decide (a.eval env = c.eval env ∧ b.eval env = d.eval env) then (1 : UInt64)
        else 0).toBitVec := by
  simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64]
  by_cases h1 : a.eval env = c.eval env <;> by_cases h2 : b.eval env = d.eval env <;>
    simp [h1, h2]

/-- **The comparison** of the top root with the key's root, and the return. -/
theorem final {k : Nat} (hp : Placed code k) (P : Pre w m₀) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b25Offset)) {r : List UInt8} (h : TopAt w m₀ st.data 16 r) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = retOf m₀ ∧
      st'.data.regs.X0 = (if r == root w then 1 else 0) ∧
      SameOutside m₀.dmem st'.data.dmem (InRange (stackBelow m₀ xmssVerifyStack) xmssVerifyStack) ∧
      Saved m₀ st'.data) st := by
  have C := h.common
  have hwf := frame_wf P C
  have hm := match_stF0 P C (known := []) trivial
  obtain ⟨gsp, g29, gmem, gk, g0⟩ := st25_facts
  refine exec_at (b25_in_code.trans hp.1 (List.cons_ne_nil _ _)) b25_exec' hwf hpc hm
    fun st' hm' hpc' => ?_
  have C' := Common.block P C hwf hm hm' (by rw [gsp]; rfl) rfl g29 (by simp [writesIn, gmem])
    (fun x _ _ => by rw [gmem]; rfl)
  have hpc'' : st'.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b27Offset) :=
    hpc'.trans (hp.label NativeRustcArm.Xmss.XmssVerify.label_10_at)
  refine NativeRustcArm.Eventually.mono (epilogue hp P hpc'' C')
    fun s ⟨h1, h2, h3, h4⟩ => ⟨h1, ?_, h3, h4⟩
  rw [h2]
  -- The key's root and the top root.
  have hpk := h.pk
  have hr0 : regBytes ((Env.ofMachine st.data [(ad m₀ fb, 5872)]).load 0 2448 8) = (pkB w).take 8 :=
    regBytes_frame (by rw [List.length_take, length_pkB]; rfl) (hpk.take 8)
  have hr1 : regBytes ((Env.ofMachine st.data [(ad m₀ fb, 5872)]).load 0 2456 8) =
      ((pkB w).drop 8).take 8 :=
    regBytes_frame (by rw [List.length_take, List.length_drop, length_pkB]; rfl)
      (by have := (hpk.drop (n := 8) (by rw [length_pkB]; decide)).take 8; rwa [ad_add] at this)
  have hkey : (r == root w) = decide ((st.data.regs.getXReg .X9).toBitVec =
      (Env.ofMachine st.data [(ad m₀ fb, 5872)]).load 0 2448 8 ∧
      (st.data.regs.getXReg .X8).toBitVec = (Env.ofMachine st.data [(ad m₀ fb, 5872)]).load 0 2456 8) := by
    generalize (Env.ofMachine st.data [(ad m₀ fb, 5872)]).load 0 2448 8 = L0 at hr0 ⊢
    generalize (Env.ofMachine st.data [(ad m₀ fb, 5872)]).load 0 2456 8 = L1 at hr1 ⊢
    have hroot : root w = regBytes L0 ++ regBytes L1 := by
      rw [hr0, hr1, root, ← List.take_add]
    rw [← h.node, hroot]
    by_cases hA : (st.data.regs.getXReg .X9).toBitVec = L0 ∧ (st.data.regs.getXReg .X8).toBitVec = L1
    · rw [hA.1, hA.2]
      simp
    · rw [decide_eq_false hA]
      apply beq_eq_false_iff_ne.mpr
      intro he
      obtain ⟨e1, e2⟩ := List.append_inj he (by rw [length_regBytes, length_regBytes])
      exact hA ⟨regBytes_inj e1, regBytes_inj e2⟩
  apply UInt64.toBitVec_inj.mp
  rw [show st'.data.regs.X0.toBitVec = (st'.data.regs.getXReg .X0).toBitVec from rfl,
    hm'.regs .X0 _ g0, eval_cmp2, hkey]
  rfl

/-- **The layers**: from block 5 with the parsed signature, the return with `xmssVerify`'s result
in X0. -/
theorem layers {k : Nat} (hp : Placed code k) (Cs : Callees) (P : Pre w m₀) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b5Offset)) (h : Parsed w m₀ st.data) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = retOf m₀ ∧
      st'.data.regs.X0 = (if Xmss.xmssVerify w then 1 else 0) ∧
      SameOutside m₀.dmem st'.data.dmem (InRange (stackBelow m₀ xmssVerifyStack) xmssVerifyStack) ∧
      Saved m₀ st'.data) st := by
  rw [xmssVerify_eq]
  refine bottom hp Cs P hpc h (fun hn st' hpc' C' => ?_) fun x r0 hs st' hpc' B => ?_
  · refine NativeRustcArm.Eventually.mono (fail hp P hpc' C') fun s ⟨h1, h2, h3, h4⟩ =>
      ⟨h1, ?_, h3, h4⟩
    rw [h2, hn]
    rfl
  · refine top hp Cs P hpc' (layerRoot_length hs) B (fun hn st'' hpc'' C'' => ?_)
      fun x' r hs' st'' hpc'' T => ?_
    · refine NativeRustcArm.Eventually.mono (fail hp P hpc'' C'') fun s ⟨h1, h2, h3, h4⟩ =>
        ⟨h1, ?_, h3, h4⟩
      rw [h2, hs]
      simp only [hn]
      rfl
    · refine NativeRustcArm.Eventually.mono (final hp P hpc'' T) fun s ⟨h1, h2, h3, h4⟩ =>
        ⟨h1, ?_, h3, h4⟩
      rw [h2, hs]
      simp only [hs']

end

end NativeRustcArm.Xmss.XmssVerify
