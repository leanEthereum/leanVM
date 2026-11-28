module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.Open1
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names

/-!
# `verify_keccak`: the committed word and its check (x86-64)

`b42`: the opening's value into R15, R14, `read_scalar` into the frame's `Option<EW>` at `408`;
`b43`: its tag; `b44` (the scratch region `2` by an alias): `EW::mul(rows[0][0], word)`, the
word's limbs spilled at `56`, `88`; `b45`, `b46`: the product against the opening's value, limb by
limb. On a failure the return with AL `0`; at `b47` (`t45`) the model's `restSum`.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeRustcVmX64.Vm.VerifyKeccak NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (DecArea TStateAt OptEWAt tstateBytes)
open NativeRustcVm.KeccakGkr (off ClaimAt WeightsAt)

@[expose] public section

/-- The values after the committed word's read. -/
def Vo (V : Vs) (v : EW) : Vs := { V with o0 := v.c0.toBitVec, o1 := v.c1.toBitVec }

/-- The values after the committed word's check. -/
def Vw (V : Vs) (v w : EW) : Vs :=
  { V with o0 := v.c0.toBitVec, o1 := v.c1.toBitVec, w0 := w.c0.toBitVec, w1 := w.c1.toBitVec }

end

public section

section
variable [Labels] {m0 : MachineData}

/-- `t44`'s alias: variable `11` (the scratch) is region `2`'s base. -/
theorem al44 {vals : Nat → BitVec 64} (h11 : vals 11 = reg m0 .r9) (m' : MachineData)
    (ret : BitVec 64) : AliasesOk t44 (envZ m0 m' 3344 3368 (rsOf m0) vals ret) := by
  intro x r o hx
  rw [show t44.aliases = [(.var 11, 2, 0)] from rfl] at hx
  simp only [List.lookup] at hx
  split at hx
  · rename_i heq
    rw [beq_iff_eq] at heq
    subst heq
    cases hx
    show vals 11 = reg m0 .r9 + BitVec.ofInt 64 0
    rw [h11]
    simp
  · cases hx

omit [Labels] in
/-- An element's words loaded from the scratch. -/
theorem ld_ewR {d : MachineData} {vals : Nat → BitVec 64} {ret : BitVec 64} {o : Nat} {x : EW}
    (h : NativeRustcVm.EWAt d.dmem (off (reg m0 .r9) o) x) :
    (envZ m0 d 3344 3368 (rsOf m0) vals ret).load 2 o 8 = x.c0.toBitVec ∧
      (envZ m0 d 3344 3368 (rsOf m0) vals ret).load 2 (o + 8) 8 = x.c1.toBitVec := by
  rw [NativeRustcVm.ewAt_iff] at h
  refine ⟨NativeRustcVmX64.Transcript.load_ofMachine (r := 2) rfl h.1,
    NativeRustcVmX64.Transcript.load_ofMachine (r := 2) rfl ?_⟩
  have e : off (reg m0 .r9) (o + 8) = off (reg m0 .r9) o + 8#64 :=
    (NativeRustcVm.addr_add_add _ _ _).symm
  show NativeRustcVm.WordAt d.dmem (off (reg m0 .r9) (o + 8)) x.c1
  rw [e]
  exact h.2

theorem eval_ne64 {env : Env} (x y : Sym) :
    (SBool.not (.cmp .eq .W64 x y)).eval env = !(x.eval env == y.eval env) := by
  simp only [SBool.eval, CmpOp.apply, low_W64]

end

theorem ew_mk (x : EW) : (⟨.ofBitVec x.c0.toBitVec, .ofBitVec x.c1.toBitVec⟩ : EW) = x := rfl

theorem beq_toBitVec (x y : UInt64) : (x.toBitVec == y.toBitVec) = (x == y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, UInt64.toBitVec_inj]

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

/-- **The committed word and its check** (`b42` to `b46`): at `b47` (`t45`). -/
theorem wordStep (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {st : MachineState} {V : Vs} {s1 : TState} {cl : KeccakClaimW} {sl ws : Array EW} {v : EW}
    (hat : At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b42Offset wrA t42 (vv m0 V) st)
    (hv : NativeRustcVm.EWAt st.data.dmem (off (fb m0) 416) v)
    (hws64 : ws.size = 64)
    (hws : NativeRustcVm.EWsAt st.data.dmem (off (reg m0 .r9) 140288) ws.toList)
    (hts : TStateAt st.data.dmem (reg m0 .rdi) a s1)
    (hrun : (NativeVm.Model.verifyKeccak (reg m0 .rsi).toNat inst output).run s =
      (restWord (reg m0 .rsi).toNat inst sl ws v cl).run s1)
    (cont : ∀ st2 w s2, At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b47Offset wrA t45 (vv m0 (Vw V v w)) st2 →
      TStateAt st2.data.dmem (reg m0 .rdi) a s2 →
      (NativeVm.Model.verifyKeccak (reg m0 .rsi).toNat inst output).run s =
        (restSum (reg m0 .rsi).toNat cl #[outClaim inst sl w]).run s2 →
      Chg m0 st.data.dmem st2.data.dmem [(0, 152), (408, 24), (3296, 48)] [(1, 0, 760)] →
      Kept st.data.dmem st2.data.dmem →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) st2) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) st := by
  have c := ctx_of hpre
  have h := lay_of hpre
  have hrc : RcAt m0 verifyKeccakStack := hpre.2.2.1
  have hl : ∀ ret, (envZ m0 st.data 3344 3368 (rsOf m0) (vv m0 V) ret).load 0 416 8 =
      v.c0.toBitVec ∧ (envZ m0 st.data 3344 3368 (rsOf m0) (vv m0 V) ret).load 0 424 8 =
      v.c1.toBitVec := fun ret ↦ ld_ew hv
  -- `b42`: `read_scalar`.
  refine stepC (T' := t43) (vals' := vv m0 (Vo V v)) hp c h hat b42_in_code (by simp [b42])
    run_b42 hat.2.mt (by decide) (oc := 48) (by decide) rfl (hrs s1) (Sk := readScalarStack)
    (by rw [vk_eq]; decide) (fun mc hmc hk hsk hso hrsp hch hkk ↦ ?_) (Lc := [(408, 24)])
    (Oc := [(1, 0, 760)]) (fun mc m' hmc hq ↦ ?_) (by decide) (by decide) (by decide)
    (by decide) (by decide) rfl rfl rfl ?_
    (fun i hi ↦ nomatch tregE (rfl : t43.reg .rax = some (.reg .rax)) hi)
    (fun i hi ↦ nomatch tregE (rfl : t43.reg .rdx = some (.reg .rdx)) hi) rfl rfl rfl
    (fun _ _ _ _ _ h ↦ by cases h) rfl fun st3 hpc3 hB3 ⟨mc, hmc, hrsp, hq, _⟩ hc3 hk3 ↦ ?_
  · have ca : CallAt m0 wrA 48 mc := ⟨hrsp, by decide, hk, hso⟩
    have rsi : reg mc .rsi = reg m0 .rdi := hmc.regs .rsi _ rfl
    have rdi : reg mc .rdi = off (fb m0) 408 := (hmc.regs .rdi _ rfl).trans (ev_frame 408)
    unfold ReadScalarPre
    dsimp only
    rw [rdi, rsi]
    refine ⟨hsk, ca.rc c hrc (by rw [vk_eq]; decide),
      Chg.ts c hch (by decide) (by decide) (by decide) hkk hts, ca.tok c (by rw [vk_eq]; decide),
      ca.outF c h (by rw [vk_eq]; decide) (by decide) (by decide), ?_⟩
    apply ca.got c (by rw [vk_eq]; decide)
    simp only [NativeRustcVm.Transcript.DecArea.region, tstateBytes]
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals first
      | (refine ⟨_, ?_, le_rfl, le_rfl⟩; solve | simp)
      | (refine ⟨(stackBelow m0 verifyKeccakStack, verifyKeccakStack + 8), by simp, ?_, ?_⟩ <;>
          rw [c.K, h.addr (by decide)] <;> have := c.sp <;> rw [vk_eq] at * <;> omega)
  · have rsi : reg mc .rsi = off (ob m0 1) 0 := (hmc.regs .rsi _ rfl).trans (off0 _).symm
    have rdi : reg mc .rdi = off (fb m0) 408 := (hmc.regs .rdi _ rfl).trans (ev_frame 408)
    obtain ⟨-, -, hso, hsv⟩ := hq
    exact chgQ hso (fun q h ↦ h.elim (fun h ↦ .inr (inR_frame rdi List.mem_cons_self h))
      fun h ↦ h.elim (fun h ↦ .inr (inR_reg rsi List.mem_cons_self h)) .inl) hsv
  · intro ret
    simp only [List.cons_append, List.nil_append, List.forall_mem_cons, Sym.eval, (hl ret).1,
      (hl ret).2]
    and_intros <;> first | rfl | exact fun _ h ↦ nomatch h
  have rsi : reg mc .rsi = reg m0 .rdi := hmc.regs .rsi _ rfl
  have rdi : reg mc .rdi = off (fb m0) 408 := (hmc.regs .rdi _ rfl).trans (ev_frame 408)
  obtain ⟨hopt, hnext, -, -⟩ := hq
  rw [rdi] at hopt
  rw [rsi] at hnext
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b42_next] at hpc3
  -- `b43`: the tag.
  refine stepJ (T' := t44) (vals' := vv m0 (Vo V v)) (o := NativeRustcVmX64.Vm.VerifyKeccak.b43Offset) hp c h ⟨hpc3, hB3⟩ b43_in_code
    (by simp [b43]) run_b43 nofun (hB3.mt 0) (by decide) rfl rfl (by vtacJ) (by decide) rfl rfl
    rfl (al44 rfl) rfl fun st4 hpc4 hB4 _ hc4 hk4 ↦ ?_
  simp only [PcOk] at hpc4
  cases hr : readScalar.run s1 with
  | none =>
    rw [hr] at hopt
    have hw : NativeRustcVm.WordAt st3.data.dmem (off (fb m0) 408) 0 := hopt
    rw [tag8 (env := envZ m0 st3.data 3344 3368 (rsOf m0) (vv m0 (Vo V v)) 0) (Or.inl rfl) hw]
      at hpc4
    exact failG hp hpre hB4 hpc4 (by decide) (by rw [hrun]; exact restWord_none hr)
  | some p =>
    obtain ⟨w, s2⟩ := p
    rw [hr] at hopt hnext
    obtain ⟨htag, hw⟩ := hopt
    rw [tag8 (env := envZ m0 st3.data 3344 3368 (rsOf m0) (vv m0 (Vo V v)) 0) (Or.inr rfl) htag]
      at hpc4
    simp only [show ((1 : UInt64) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte] at hpc4
    rw [toff, show 408 + 8 = 416 from rfl] at hw
    have hc34 := hc3.trans hc4
    have hw4 : NativeRustcVm.EWAt st4.data.dmem (off (fb m0) 416) w :=
      NativeRustcVm.Layout.EWAt.of_same hw (Chg.frame c hc4 (by decide) (by decide)
        (o := 416) (n := 16) (by decide) (by decide)) le_rfl
    have hws4 : NativeRustcVm.EWsAt st4.data.dmem (off (reg m0 .r9) 140288) ws.toList :=
      Chg.ewsR c hc34 (by decide) (by decide) (i := 2) (o := 140288) (by decide) (by decide)
        (by rw [Array.length_toList, hws64]; decide) (by rw [Array.length_toList, hws64]; decide)
        hws
    have hts2 : TStateAt st4.data.dmem (reg m0 .rdi) a s2 :=
      Chg.ts c hc4 (by decide) (by decide) (by decide) hk4 (hnext w s2 rfl)
    have h0 : NativeRustcVm.EWAt st4.data.dmem (off (reg m0 .r9) 140288) (ws.getD 0 0) := by
      have := NativeRustcVm.ewsAt_getElem hws4 (i := 0) (by simp [hws64])
      simpa [Array.getD_eq_getD_getElem?, hws64] using this
    have hr0 := fun ret ↦ ld_ewR (vals := vv m0 (Vo V v)) (ret := ret) h0
    have hw0 := fun ret ↦ ld_ew (rs := rsOf m0) (vals := vv m0 (Vo V v)) (ret := ret) hw4
    rw [NativeRustcVmX64.Vm.VerifyKeccak.b43_next] at hpc4
    -- `b44`: `EW::mul`.
    refine stepC (hwfS := fun _ ↦ h.wf hB4.kept)
      (T' := t45) (vals' := vv m0 (Vw V v w)) hp c h ⟨hpc4, hB4⟩ b44_in_code
      (by simp [b44]) run_b44 hB4.mt (by decide) (oc := 48) (by decide) rfl hmul
      (Sk := ewMulStack) (by rw [vk_eq]; decide) (fun mc hmc hk hsk hso hrsp hch hkk ↦ hsk)
      (Lc := []) (Oc := []) (fun mc m' hmc hq ↦ ?_) (by decide) (by decide) (by decide)
      (by decide) (by decide) rfl rfl rfl ?_
      (fun i hi ↦ nomatch tregE (rfl : t45.reg .rax = some (.reg .rax)) hi)
      (fun i hi ↦ nomatch tregE (rfl : t45.reg .rdx = some (.reg .rdx)) hi) rfl rfl rfl
      (fun _ _ _ _ _ h ↦ by cases h) rfl fun st5 hpc5 hB5 ⟨mc, hmc, hrsp, hq, _⟩ hc5 hk5 ↦ ?_
    · obtain ⟨-, -, hso, hsv⟩ := hq
      exact chgQ hso (fun q h ↦ .inl h) hsv
    · intro ret
      simp only [List.cons_append, List.nil_append, List.forall_mem_cons, Sym.eval, (hw0 ret).1,
        (hw0 ret).2]
      and_intros <;> first | rfl | exact fun _ h ↦ nomatch h
    -- The product.
    have hprod : ewArg (reg st5.data .rax) (reg st5.data .rdx) = ws.getD 0 0 * w := by
      have rdi : reg mc .rdi = (ws.getD 0 0).c0.toBitVec := (hmc.regs .rdi _ rfl).trans (hr0 _).1
      have rsi : reg mc .rsi = (ws.getD 0 0).c1.toBitVec := (hmc.regs .rsi _ rfl).trans (hr0 _).2
      have rdx : reg mc .rdx = w.c0.toBitVec := (hmc.regs .rdx _ rfl).trans (hw0 _).1
      have rcx : reg mc .rcx = w.c1.toBitVec := (hmc.regs .rcx _ rfl).trans (hw0 _).2
      obtain ⟨hax, hdx, -, -⟩ := hq
      rw [rdi, rsi, rdx, rcx, ew_mk, ew_mk] at hax hdx
      rw [hax, hdx]
      rfl
    rw [NativeRustcVmX64.Vm.VerifyKeccak.b44_next] at hpc5
    -- `b45`: the low limbs.
    refine stepJ (T' := t45) (vals' := vv m0 (Vw V v w)) (o := NativeRustcVmX64.Vm.VerifyKeccak.b45Offset) hp c h ⟨hpc5, hB5⟩ b45_in_code
      (by simp [b45]) run_b45 nofun (hB5.mt 0) (by decide) rfl rfl (by vtacJ) (by decide) rfl rfl
      rfl (fun _ _ _ _ _ h ↦ by cases h) rfl fun st6 hpc6 hB6 hm6 hc6 hk6 ↦ ?_
    simp only [PcOk] at hpc6
    have hax5 : reg st5.data .rax = (ws.getD 0 0 * w).c0.toBitVec := by
      have := congrArg (fun e : EW ↦ e.c0.toBitVec) hprod
      exact this
    have hdx5 : reg st5.data .rdx = (ws.getD 0 0 * w).c1.toBitVec := by
      have := congrArg (fun e : EW ↦ e.c1.toBitVec) hprod
      exact this
    rw [eval_ne64, show (Sym.reg .rax).eval (envZ m0 st5.data 3344 3368 (rsOf m0)
        (vv m0 (Vw V v w)) 0) = (ws.getD 0 0 * w).c0.toBitVec from hax5,
      show (Sym.var 21).eval (envZ m0 st5.data 3344 3368 (rsOf m0)
        (vv m0 (Vw V v w)) 0) = v.c0.toBitVec from rfl, beq_toBitVec] at hpc6
    have hk46 := NativeRustcVmX64.Transcript.kept_trans hk5 hk6
    by_cases hc0 : (ws.getD 0 0 * w).c0 = v.c0
    · simp only [hc0, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc6
      rw [NativeRustcVmX64.Vm.VerifyKeccak.b45_next] at hpc6
      have hdx6 : reg st6.data .rdx = (ws.getD 0 0 * w).c1.toBitVec :=
        (hm6.regs .rdx _ rfl).trans hdx5
      -- `b46`: the high limbs.
      refine stepJ (T' := t45) (vals' := vv m0 (Vw V v w)) (o := NativeRustcVmX64.Vm.VerifyKeccak.b46Offset) hp c h ⟨hpc6, hB6⟩
        b46_in_code (by simp [b46]) run_b46 nofun (hB6.mt 0) (by decide) rfl rfl (by vtacJ)
        (by decide) rfl rfl rfl (fun _ _ _ _ _ h ↦ by cases h) rfl
        fun st7 hpc7 hB7 _ hc7 hk7 ↦ ?_
      simp only [PcOk] at hpc7
      rw [eval_ne64, show (Sym.reg .rdx).eval (envZ m0 st6.data 3344 3368 (rsOf m0)
          (vv m0 (Vw V v w)) 0) = (ws.getD 0 0 * w).c1.toBitVec from hdx6,
        show (Sym.var 22).eval (envZ m0 st6.data 3344 3368 (rsOf m0)
          (vv m0 (Vw V v w)) 0) = v.c1.toBitVec from rfl, beq_toBitVec] at hpc7
      by_cases hc1 : (ws.getD 0 0 * w).c1 = v.c1
      · simp only [hc1, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc7
        have hok : (ws.getD 0 0 * w == v) = true := by
          rw [ew_beq, hc0, hc1, beq_self_eq_true, beq_self_eq_true, Bool.and_self]
        refine cont st7 w s2 ⟨hpc7.trans (by rw [NativeRustcVmX64.Vm.VerifyKeccak.b46_next]), hB7⟩
          (Chg.ts c (hc5.trans (hc6.trans hc7)) (by decide) (by decide) (by decide)
            (NativeRustcVmX64.Transcript.kept_trans hk46 hk7) hts2)
          (hrun.trans (restWord_ok hr hok)) ?_
          (NativeRustcVmX64.Transcript.kept_trans hk3 (NativeRustcVmX64.Transcript.kept_trans hk4
            (NativeRustcVmX64.Transcript.kept_trans hk46 hk7)))
        exact Chg.mono c (hc34.trans (hc5.trans (hc6.trans hc7))) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)
      · have hbad : (ws.getD 0 0 * w == v) = false := by
          rw [ew_beq, hc0, beq_self_eq_true, Bool.true_and]
          exact beq_false_of_ne hc1
        simp only [beq_false_of_ne hc1, Bool.not_false, ↓reduceIte] at hpc7
        exact failG hp hpre hB7 hpc7 (by decide) (by rw [hrun]; exact restWord_bad hr hbad)
    · have hbad : (ws.getD 0 0 * w == v) = false := by
        rw [ew_beq, beq_false_of_ne hc0, Bool.false_and]
      simp only [beq_false_of_ne hc0, Bool.not_false, ↓reduceIte] at hpc6
      exact failG hp hpre hB6 hpc6 (by decide) (by rw [hrun]; exact restWord_bad hr hbad)

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back
