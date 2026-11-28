module

public import NativeRustcVmArm.Code.Vm.BufEW36Extend.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Fin2

/-!
# `verify_keccak`: the output point, `low`

`b66` (from `outS`, region 1 the `KeccakOutW`): `out.point` emptied, extended by the four low
challenges; `b67`: its verdict. At `b68` (`AtZ`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt)

@[expose] public section

/-- **`out.point` holds `low`** (`b68`). -/
structure AtZ [Labels] (a : DecArea) (s : TState) (cs : Array ColumnClaimW)
    (inst output : Array EW) (m0 m : MachineData) (s' : TState) (cj : KeccakClaimW)
    (outs : Array ColumnClaimW) (low sl xs : Array EW) : Prop where
  fr : VFr m0 m
  x23 : (m.regs.getXReg .X23).toBitVec = loc m0 1248
  x24 : (m.regs.getXReg .X24).toNat = cj.point.size
  w72 : NativeRustcVm.WordAt m.dmem (loc m0 72) m0.regs.X7
  pk : NativeRustcVm.WordAt m.dmem (loc m0 88) (packW m0)
  ts : TStateAt m.dmem (tA m0) a s'
  cls : NativeRustcVm.Layout.ClaimsWAt m.dmem (clA m0) (cs ++ outs)
  claim : ClaimAt m.dmem (loc m0 960) cj
  psz : cj.point.size = inst.size - 4 + 1
  lowsz : low.size = 4
  slsz : sl.size = 6
  slot : NativeRustcVm.EWsAt m.dmem (loc m0 2496) sl.toList
  xsz : xs.size = 64
  slices : NativeRustcVm.EWsAt m.dmem (oA m0 + BitVec.ofNat 64 584) xs.toList
  obuf : NativeRustcVm.BufEWAt m.dmem (oA m0) 36 low.toList
  run : run0 s inst output m0 =
    some ((outs, low ++ cj.point.extract 0 (m0.regs.X1.toNat - 4) ++ sl, xs), s')

/-- The environment of `b66`: the frame and the `KeccakOutW`. -/
abbrev envO (m0 m : MachineData) : Env := Env.ofMachine m [(fb m0, 3360), (oA m0, 1608)]

/-- The registers `b67` keeps. -/
def o3L : List XReg := [.X23, .X24]

end

public section

section
variable [Labels] {a : DecArea} {s : TState} {cs : Array ColumnClaimW} {inst output : Array EW}
  {m0 : MachineData}

theorem envO_wf (h : P0 a s cs inst output m0) (hn : Nums a inst m0) {m : MachineData}
    (hfr : VFr m0 m) : (envO m0 m).WF := by
  have hN := hn.hN
  have hSP := m0.regs.SP.toNat_lt
  have hfm : Mapped m.dmem (fb m0) 3360 :=
    fun i hi ↦ hfr.kept _ (frame_mapped hn.stk (by decide) i hi)
  refine Env.wf_of ⟨⟨hfm, base_noWrap (by omega)⟩, ⟨Mapped.kept' (ok_out h) hfr.kept, hn.oW⟩,
    trivial⟩ (List.Pairwise.cons (fun e he ↦ by
      simp only [List.mem_singleton] at he; subst he
      unfold Apart; simp only; rw [fb_toNat hn.hN]
      obtain h1 | h1 := hn.oS <;> omega) (List.pairwise_singleton _ _))

theorem matchO {m : MachineData} (hfr : VFr m0 m) (hn : Nums a inst m0)
    (h72 : NativeRustcVm.WordAt m.dmem (loc m0 72) m0.regs.X7) : Match (envO m0 m) outS m :=
  match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hn.stk (by decide) (by decide),
      ⟨rfl, ⟨fun h ↦ absurd h (by decide), trivial⟩⟩⟩
    (by rw [hfr.sp]; simp [Sym.eval]) trivial trivial trivial
    ⟨by
      show (envO m0 m).load 0 72 8 = oA m0 + BitVec.ofInt 64 0
      rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
      exact Sumcheck.load_word h72, trivial⟩

/-- A block's writes at the `KeccakOutW`'s first `n` bytes. -/
theorem chg_out {m st : MachineData} {S : SState} (hm : Match (envO m0 m) S st)
    (hwf : (envO m0 m).WF) {n : Nat}
    (hw : S.mem.all (fun w ↦ w.r == 1 && decide (w.off + w.n ≤ n)) = true) :
    Chg m0 [] [(3, 0, n)] m.dmem st.dmem := by
  intro q hq
  refine hm.sameOutside hwf q fun ⟨w, hw', b, sz, hb, h1, h2⟩ ↦ hq ?_
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
  obtain ⟨hr, hle⟩ := hw w hw'
  rw [hr] at hb
  simp only [Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  exact .inr (.inr ⟨(3, 0, n), List.mem_singleton_self _, by simp only [ob]; omega,
    by simp only [ob]; omega⟩)

/-- A block's writes at the `KeccakOutW` are to the outputs. -/
theorem wOk_out (hn : Nums a inst m0) {m : MachineData} {S : SState}
    (hw : S.mem.all (fun w ↦ w.r == 1 && decide (w.off + w.n ≤ 1608)) = true) :
    ∀ w ∈ S.mem, WriteOk (envO m0 m) 3360 slots (outs m0) w := by
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
  intro w hw'
  obtain ⟨hr, hle⟩ := hw w hw'
  refine .inr ⟨by omega, fun b sz hb ↦ ?_⟩
  rw [hr] at hb
  simp only [Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  refine ⟨hle, fun i hi ↦ ob_outs hn (i := 3) (by decide) ?_ ?_⟩ <;>
    simp only [ob, osz] <;> rw [oN hn hi] <;> omega

end

variable [Host] {k : Nat} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output : Array EW} {m0 : MachineData}

/-- **`out.point`, `low`** (`b66`, `b67`). -/
theorem stepOut1 (hp : Placed code k) (h : P0 a s cs inst output m0) (hn : Nums a inst m0)
    (hext : Spec (Labels.label NativeRustcVmArm.Vm.BufEW36Extend.entryLabel) (BufEWExtendPre 36) (BufEWExtendPost 36))
    {m : MachineData} {s3 : TState} {cj : KeccakClaimW} {outs : Array ColumnClaimW}
    {low sl xs : Array EW} (hx : AtX a s cs inst output m0 m s3 cj outs low sl xs)
    (cont : ∀ m', AtZ a s cs inst output m0 m' s3 cj outs low sl xs →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b68Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b66Offset)⟩ := by
  have hN := hn.hN
  have hwf := envO_wf h hn hx.fr
  have hm0 := matchO hx.fr hn hx.w72
  have l72 : (Sym.load 0 72 8).eval (envO m0 m) = oA m0 := Sumcheck.load_word hx.w72
  refine callStep hn (b66_in_code.trans hp.1 (by simp [b66])) run_b66 hx.fr hm0 hwf rfl
    (wOk_out hn (by decide)) (N' := bufExtendStack) (lo := 0) (n := 0) (by decide) (by decide)
    hext (fun st hm1 hfr1 ↦ ?_) (fun st m' hm1 hfr1 hq ↦ ?_)
    fun st m2 hm1 hfr1 hq hfr2 hcs ↦ ?_
  all_goals
    have hb0 : Chg m0 [] [(3, 0, 8)] m.dmem st.dmem := chg_out hm1 hwf (by decide)
    have e0 : st.regs.X0.toBitVec = oA m0 := by
      rw [show st.regs.X0 = st.regs.getXReg .X0 from rfl, hm1.regs .X0 _ rfl]; exact l72
    have e1 : st.regs.X1.toBitVec = loc m0 3176 := reg_loc hm1 (r := .X1) (o := 3176) rfl
    have e2 : st.regs.X2.toNat = low.toList.length := by
      rw [show st.regs.X2 = (4 : UInt64) from reg_of hm1 (r := .X2) (v := .lit 4) rfl rfl]
      simp [hx.lowsz]
    have hw0 : NativeRustcVm.WordAt st.dmem (oA m0) 0 := by
      have := Sumcheck.Match.wordAt_write hm1 (r := 1) (o := 0) (v := .lit 0) rfl (by decide)
        (by decide)
      rwa [NativeRustcVm.addr_add_zero] at this
    have hlow : NativeRustcVm.EWsAt st.dmem (loc m0 3176) low.toList :=
      hb0.ews hn (by decide) (o := 3176) (k := 64) (by decide) (by decide)
        (by simp [hx.lowsz]) hx.lowv
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> (try rw [e0]) <;> (try rw [e1]) <;> (try rw [e2])
    · rw [NativeRustcVm.wordOf_of_wordAt hw0]; decide
    · have := readable_of (ok_out h) hn.oW hfr1.kept (o := 0) (n := 584) (by decide)
      rwa [NativeRustcVm.addr_add_zero] at this
    · exact ⟨frame_mapped' hn hfr1 (by simp [hx.lowsz]), loc_noWrap hn (by simp [hx.lowsz])⟩
    · unfold Apart; rw [loc_toNat hn.hN (by decide)]; simp only [Array.length_toList, hx.lowsz]
      obtain h1 | h1 := hn.oS <;> omega
  · obtain ⟨-, hs, hsv⟩ := hq
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q hq ↦ ?_, hsv⟩
    rw [e0] at hq
    rcases hq with hq | hq
    · have := hn.oW
      have h1 := inR_nat (n := 584) (by omega) hq
      exact .inr (.inr (ob_outs hn (i := 3) (by decide) (by simp only [ob]; omega)
        (by simp only [ob, osz]; omega)))
    · exact .inl hq
  · obtain ⟨hpost, hs, hsv⟩ := hq
    have hbo : NativeRustcVm.bufEWOf st.dmem (oA m0) = [] := by
      unfold NativeRustcVm.bufEWOf; rw [NativeRustcVm.wordOf_of_wordAt hw0]; rfl
    have hsl : (slice st st.regs.X1 st.regs.X2).toList = low.toList := by
      unfold slice; rw [e1, e2, NativeRustcVm.ewsOf_of_ewsAt hlow]
    rw [e0, NativeRustcVm.wordOf_of_wordAt hw0, e2, hbo, hsl] at hpost
    simp only [UInt64.toNat_zero, Nat.zero_add, Array.length_toList, hx.lowsz,
      show 4 ≤ 36 from by decide, ↓reduceIte, List.nil_append] at hpost
    obtain ⟨hx0, hbuf⟩ := hpost
    have hc : Chg m0 [] [(3, 0, 584)] st.dmem m2.dmem := by
      intro q hq
      refine hs q fun h1 ↦ hq ?_
      rw [e0] at h1
      rcases h1 with h1 | h1
      · exact ws_ob0 hn (i := 3) (n := 584) (by decide) (by decide) (by decide) (by decide) h1
      · exact (inRange_zero h1).elim
    have T := hb0.trans hc
    have hk : Kept m.dmem m2.dmem := kept_tr (hm1.kept hwf) hsv.2.2
    rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b66Offset + b66.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b67Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b66_next]]
    refine failBranchF hp hn (b67_in_code.trans hp.1 (by simp [b67])) run_b67 hfr2 rfl rfl
      (L := o3L) (by decide) (b := true)
      (condW0 (by rw [Env.ofMachine_regs, gx0, hx0]; rfl)) (fun hf ↦ nomatch hf)
      fun _ m3 hfr3 hd3 hk3 ↦ ?_
    have g : ∀ r ∈ o3L, m3.regs.getXReg r = m2.regs.getXReg r := hk3
    simp only [o3L, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g
    obtain ⟨g23, g24⟩ := g
    rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b67Offset + b67.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b68Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b67_next]]
    refine cont m3 ⟨hfr3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hx.psz, hx.lowsz, hx.slsz, ?_, hx.xsz, ?_,
        ?_, hx.run⟩
    · rw [g23, hcs .X23 rfl, Match.reg_eq hm0 hm1 (r := .X23) rfl rfl]; exact hx.x23
    · rw [g24, hcs .X24 rfl, Match.reg_eq hm0 hm1 (r := .X24) rfl rfl]; exact hx.x24
    all_goals rw [hd3]
    · exact T.word hn (by decide) (by decide) (by decide) hx.w72
    · exact T.word hn (by decide) (by decide) (by decide) hx.pk
    · exact T.ts hn hk (by decide) (by decide) (by decide) hx.ts
    · exact T.cls hn (by decide) (by decide) (by decide) hx.cls
    · exact T.claim hn (by decide) (by decide) (by decide) hx.claim
    · exact T.ews hn (by decide) (o := 2496) (k := 96) (by decide) (by decide)
        (by simp [Array.length_toList, hx.slsz]) hx.slot
    · exact T.ewsOut hn (by decide) (by decide) (i := 3) (o := 584) (k := 1024)
        (by decide) (by decide) (by decide) (by decide) (by simp [Array.length_toList, hx.xsz])
        hx.slices
    · exact hbuf

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
