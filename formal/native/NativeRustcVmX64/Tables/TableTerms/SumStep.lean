module

public import NativeRustcVmX64.Tables.TableTerms.Point
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `table_terms`: table `i`'s sum (x86-64)

`b12` multiplies the weight by the sum of the two dot products (`EW::mul`), `b13` adds the product
to the running sum, advances the cursor and every walk, and goes back to the loop head before table
`i + 1` (or on to `b14` after the sixth table): the model's fold over the first `i + 1` rows
(`sum_step`).
-/

namespace NativeRustcVmX64.Tables.TableTerms

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVm.Bus
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.TableTerms
open NativeRustcVm (wordOf ewsOf ewOf)

public section

theorem ew_eta (x : EW) : (⟨UInt64.ofBitVec x.c0.toBitVec, UInt64.ofBitVec x.c1.toBitVec⟩ : EW) = x :=
  rfl

theorem ew_add_c0 (x y : EW) : (x + y).c0 = x.c0 ^^^ y.c0 := rfl
theorem ew_add_c1 (x y : EW) : (x + y).c1 = x.c1 ^^^ y.c1 := rfl

theorem toBitVec_xor' (a b : UInt64) : (a ^^^ b).toBitVec = a.toBitVec ^^^ b.toBitVec := rfl

theorem ofNat_add' (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

variable [Host] {k : Nat} {a : DecArea} {s : TState} {heights : Array Nat}
  {forms : Array (Array FormW)} {m0 : MachineData}

/-- **Table `i`'s sum**, to the loop head before table `i + 1`. -/
theorem sum_step (hp : Placed code k) (h : TableTermsPre a s heights forms m0)
    (hh : heights.size = 6) (hf : forms.size = 6)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {i : Nat} (hi : i < 6) {c : Nat} {f : EW} {o : Array (Array EW × Array EW)} {si : TState}
    {xs : Array EW} {s' : TState} {d : MachineData}
    (hrun : preRun heights forms m0 i s = some ((c, f, o), si)) (hcur : c = cursorAt i)
    (hrs : (readScalars (tb i).width).run si = some (xs, s'))
    (hb : Bd m0 272 N slots (outs m0) 8 d)
    (hfw : FW m0 d (LA m0 i f ++ (ncW i ++ ewW 80 (dotC m0 i (cursorAt i) xs) ++ wW (wt m0 i))))
    (H : It a m0 i o xs s' d)
    (hpt : NativeRustcVm.BufEWAt d.dmem (evi m0 i) 30 (ptI heights m0 i).toList)
    (h14 : reg d .r14 = (dotF m0 (forms.getD i #[]) xs).c0.toBitVec)
    (h13 : reg d .r13 = (dotF m0 (forms.getD i #[]) xs).c1.toBitVec)
    (h15 : reg d .r15 = fA m0 + BitVec.ofNat 64 (11864 + 17784 * i))
    (hbx : reg d .rbx = evi m0 i) (hbp : reg d .rbp = BitVec.ofNat 64 (16 + 40 * i))
    (h12 : reg d .r12 = BitVec.ofNat 64 (8 * i))
    {R : MachineState → Prop}
    (cont : ∀ acc' d', preRun heights forms m0 (i + 1) s = some (acc', s') →
      Head a s heights forms m0 (i + 1) acc' s' d' →
      (i + 1 < 6 → Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b1Offset)⟩) ∧
      (i + 1 = 6 → Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b14Offset)⟩)) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b12Offset)⟩ := by
  have hS := Pre.stack h
  -- `b12`: `EW::mul`'s arguments.
  let ra := (Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b12Offset + b12.length)).toBitVec
  have hwf : (E m0 d [] ra).WF := wf_nil h hb.fr.kept
  have hm : Match (E m0 d [] ra) sF d := match_body hb ⟨rfl, trivial⟩ trivial
  refine exec_then (infix_of b12_in_code (by simp [b12]) hp) exit_b12 hwf (fun _ _ ↦ rfl) hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨miss1, mid1, W1, -, rdi1, rsi1, rdx1, rcx1, -, -, k1⟩ := ok_b12
  have hb1 := (blockB h hb hwf hm1 mid1 W1 nofun).1
  have hs1 := same_block hwf hm1 (writesIn_of_mid mid1) (belowRet_of_mid mid1) W1
    (X := fun _ ↦ False) nofun
  have hW1 : ∀ q, (NativeRustcVm.InRange (stackBelow m0 272) 272 q ∨ False) →
      NativeRustcVm.InRange (stackBelow m0 N) N q :=
    fun q hq ↦ hq.elim (fr_stack h) False.elim
  have it1 := H.step h hi (hm1.kept hwf) hs1 fun q hq ↦ .inl (hW1 q hq)
  have pt1 := pt_keep h hi hs1 hW1 hpt
  have hLb : ∀ p ∈ LA m0 i f ++ (ncW i ++ ewW 80 (dotC m0 i (cursorAt i) xs) ++ wW (wt m0 i)),
      8 ≤ p.1 ∧ p.1 + 8 ≤ 280 := fun p hp ↦ by
    rcases List.mem_append.mp hp with hp | hp
    · exact ⟨(fwL_le p hp).1, (fwL_le p hp).2.1⟩
    · simp only [List.mem_append, ncW, ewW, wW, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with ((rfl | rfl) | rfl | rfl) | rfl | rfl <;> exact ⟨by simp, by simp⟩
  have fw1 := fw_blockU hwf hm1 (writesIn_of_mid mid1) miss1 rfl (fun p hp ↦ (hLb p hp).2) hfw
  have rg1 : ∀ {r : Reg64} {v : Sym}, (after b12 sF).reg r = some v →
      reg st1.data r = v.eval (E m0 d [] ra) := fun hv ↦ hm1.regs _ _ hv
  have fwW := FW.right (FW.right hfw)
  have fw80 := FW.right (FW.left (FW.right hfw))
  have w72 : NativeRustcVm.WordAt d.dmem (off (fb m0) 72) (wt m0 i).c0 :=
    fwW (72, (wt m0 i).c0) List.mem_cons_self
  have w64 : NativeRustcVm.WordAt d.dmem (off (fb m0) 64) (wt m0 i).c1 :=
    fwW (64, (wt m0 i).c1) (List.mem_cons_of_mem _ List.mem_cons_self)
  have hpS := hb1
  have hle : 272 + ewMulStack ≤ N := by rw [N_eq]; decide
  have hpre : EWMulPre st1.data := hb1.stackOk_at hS (Nat.zero_le _) (by simpa using hle)
  simp only [PcOk] at hpc1
  refine call_then (env := E m0 d [] ra) hpc1 hmul hpre fun st2 hpc2 hrsp2 hq2 ↦ ?_
  obtain ⟨q0, q1, q2, q3⟩ := hq2
  have eW : (⟨UInt64.ofBitVec (reg st1.data .rdi), UInt64.ofBitVec (reg st1.data .rsi)⟩ : EW) =
      wt m0 i := by
    rw [rg1 rdi1, rg1 rsi1, ld0 w72, ld0 w64]
  have eS : (⟨UInt64.ofBitVec (reg st1.data .rdx), UInt64.ofBitVec (reg st1.data .rcx)⟩ : EW) =
      dotC m0 i (cursorAt i) xs + dotF m0 (forms.getD i #[]) xs := by
    rw [rg1 rdx1, rg1 rcx1, eval_xor', eval_xor', eval_reg, eval_reg, h14, h13,
      ld0 (fw80 (80, (dotC m0 i (cursorAt i) xs).c0) List.mem_cons_self),
      ld0 (fw80 (80 + 8, (dotC m0 i (cursorAt i) xs).c1) (List.mem_cons_of_mem _ List.mem_cons_self))]
    show (⟨_, _⟩ : EW) = ⟨_ ^^^ _, _ ^^^ _⟩
    rw [← toBitVec_xor', ← toBitVec_xor', UInt64.xor_comm, UInt64.xor_comm (dotF _ _ _).c1]
  rw [eW, eS] at q0 q1
  have hb1' : Bd m0 272 N slots (outs m0) 0 st1.data := hb1
  obtain ⟨hb2, fw2, it2⟩ := pure_call h hi hb1' hle q3 hrsp2
    (NativeRustcVm.SameOutside.mono q2 fun q hq ↦ .inr hq) hLb fw1 it1
  have pt2 := pt_keep h hi (NativeRustcVm.SameOutside.mono q2 fun q hq ↦ hq) (W := fun q ↦
    NativeRustcVm.InRange (stackBelow st1.data ewMulStack) ewMulStack q)
    (fun q hq ↦ callee_stack h hb1' hle hq) pt1
  have cs2 : ∀ r, calleeSaved r = true → reg st2.data r = reg st1.data r := q3.1
  have kr1 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r15], reg st1.data r = reg d r :=
    fun r hr ↦ keeps_reg hm1 k1 hr
  -- The model's step.
  subst hcur
  let p := wt m0 i * (dotC m0 i (cursorAt i) xs + dotF m0 (forms.getD i #[]) xs)
  let acc' : Acc := (cursorAt i + (tb i).nConstraints, f + p, o.push (ptI heights m0 i, xs))
  have hrun' : preRun heights forms m0 (i + 1) s = some (acc', s') := by
    rw [preRun_succ hh hf hi, hrun]
    show (stp m0 (cursorAt i, f, o) _).run si = _
    rw [stp_run, hrs]
    rfl
  -- `b13`: the sum, the walks.
  let ra3 := (Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b13Offset + b13.length)).toBitVec
  have hwf3 : (E m0 st2.data [] ra3).WF := wf_nil h hb2.fr.kept
  have hm3 : Match (E m0 st2.data [] ra3) sF st2.data := match_body hb2 ⟨rfl, trivial⟩ trivial
  refine at_pc (hpc2.trans (addr_eq (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.TableTerms.b12_next)))
    (exec_then (infix_of b13_in_code (by simp [b13]) hp) exit_b13 hwf3 nofun hm3
      fun st3 hm3' hpc3 ↦ ?_)
  obtain ⟨miss3, mid3, W3, -, w16, rcx3, rdx3, r15_3, rax3, r12_3, r13_3, r14_3, rbx3, rbp3⟩ :=
    ok_b13
  have hb3 := (blockB h hb2 hwf3 hm3' mid3 W3 nofun).1
  have hs3 := same_block hwf3 hm3' (writesIn_of_mid mid3) (belowRet_of_mid mid3) W3
    (X := fun _ ↦ False) nofun
  have it3 := it2.step h hi (hm3'.kept hwf3) hs3 fun q hq ↦ .inl (hW1 q hq)
  have pt3 := pt_keep h hi hs3 hW1 pt2
  have fw3 := fw_blockU hwf3 hm3' (writesIn_of_mid mid3) miss3 rfl (fun p hp ↦ (cws_le p hp).2.1)
    (FW.left (FW.left (FW.left fw2)))
  have rg3 : ∀ {r : Reg64} {v : Sym}, (after b13 sF).reg r = some v →
      reg st3.data r = v.eval (E m0 st2.data [] ra3) := fun hv ↦ hm3'.regs _ _ hv
  have fwl := FW.right (FW.left (FW.left fw2))
  have fwn := FW.left (FW.left (FW.right fw2))
  have r2 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r15], reg st2.data r = reg d r := fun r hr ↦ by
    rw [cs2 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> rfl), kr1 r hr]
  have e16 : (Sym.bin .add .W64 (.lit 1968) (.reg .rbx)).eval (E m0 st2.data [] ra3) =
      evi m0 (i + 1) := by
    rw [eval_lit_add, eval_reg, r2 .rbx (by simp), hbx]
    unfold evi
    rw [NativeRustcVm.addr_add_add, show 1968 * i + 1968 = 1968 * (i + 1) by ring]
  have hcl := cursor_le hi
  have hc : c13.eval (E m0 st2.data [] ra3) = decide (i + 1 < 6) := by
    unfold c13
    rw [eval_not']
    simp only [SBool.eval, Sym.eval, BinOp.apply, CmpOp.apply, low_W64, ext_W64]
    rw [show (E m0 st2.data [] ra3).regs .rbp = reg st2.data .rbp from rfl, r2 .rbp (by simp), hbp,
      show (40#64 : BitVec 64) = BitVec.ofNat 64 40 from rfl,
      show (256#64 : BitVec 64) = BitVec.ofNat 64 256 from rfl, ofNat_add']
    by_cases h5 : i + 1 < 6
    · have : ¬ (BitVec.ofNat 64 (40 + (16 + 40 * i)) = BitVec.ofNat 64 256) := fun he ↦ by
        have := congrArg BitVec.toNat he
        rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at this
        omega
      simp [this, h5]
    · have : BitVec.ofNat 64 (40 + (16 + 40 * i)) = BitVec.ofNat 64 256 := by
        congr 1; omega
      simp [this, h5]
  simp only [PcOk, hc] at hpc3
  have HH : Head a s heights forms m0 (i + 1) acc' s' st3.data := by
    refine ⟨hb3, fw3, wroteW hm3' (by omega) w16 e16, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrun',
      (cursorAt_succ i).symm, by simp [acc', it3.osz], it3.ts, ?_⟩
    · rw [rg3 r14_3, eval_lit_add, eval_reg, r2 .rbp (by simp), hbp, ofNat_add',
        show 16 + 40 * i + 40 = 16 + 40 * (i + 1) by ring]
    · rw [rg3 rbp3]; rfl
    · rw [rg3 r13_3, eval_lit_add, eval_reg, r2 .r15 (by simp), h15, NativeRustcVm.addr_add_add,
        show 11864 + 17784 * i + 17784 = 11864 + 17784 * (i + 1) by ring]
    · rw [rg3 rax3, eval_lit_add, eval_reg, r2 .r12 (by simp), h12, ofNat_add',
        show 8 * i + 8 = 8 * (i + 1) by ring]
    · rw [rg3 r15_3, eval_add',
        ld0 (fwn (96, .ofBitVec (BitVec.ofNat 64 (tb i).nConstraints)) List.mem_cons_self),
        ld0 (fwn (104, .ofBitVec (BitVec.ofNat 64 (cursorAt i)))
          (List.mem_cons_of_mem _ List.mem_cons_self)), cursorAt_succ]
      show BitVec.ofNat 64 (tb i).nConstraints + BitVec.ofNat 64 (cursorAt i) = _
      rw [ofNat_add', Nat.add_comm]
    · rw [rg3 rdx3, eval_xor', ld0 (lw120 fwl), eval_reg, q0]
      show _ = (f.c0 ^^^ p.c0).toBitVec
      rw [toBitVec_xor']
      rfl
    · rw [rg3 rcx3, eval_xor', ld0 (lw128 fwl), eval_reg, q1]
      show _ = (f.c1 ^^^ p.c1).toBitVec
      rw [toBitVec_xor']
      rfl
    · intro j hj
      show TableEvalAt _ _ (o.push (ptI heights m0 i, xs))[j]
      have hj' : j < o.size + 1 := by
        have : acc'.2.2.size = o.size + 1 := Array.size_push _
        omega
      rcases Nat.lt_or_ge j o.size with hlt | hge
      · rw [Array.getElem_push_lt hlt]
        exact it3.evs j hlt
      · have hji : j = o.size := by omega
        subst hji
        rw [Array.getElem_push_eq]
        rw [it3.osz]
        exact ⟨pt3, it3.vals⟩
  have hc2 := cont acc' st3.data hrun' HH
  by_cases h5 : i + 1 < 6
  · simp only [h5, decide_true, ↓reduceIte] at hpc3
    exact at_pc (hpc3.trans (lbl_1 hp)) (hc2.1 h5)
  · simp only [h5, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc3
    exact at_pc (hpc3.trans (addr_eq (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.TableTerms.b13_next))) (hc2.2 (by omega))

end

end NativeRustcVmX64.Tables.TableTerms
