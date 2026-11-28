module

public import NativeRustcVmArm.KeccakGkr.KeccakOpen.Exit

/-!
# `keccak_open`: the return after the fold

`b93` writes the value from the frame's `16` into the result at `8` and jumps to the return
with tag `1`; the slot point, row `0` of the folded rows (`Fr_six`) and the `TState` are kept
(`some_exit`).
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays
open NativeRustcVmArm.Vm.KeccakOpen
open LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeRustcVm (Region InAny)
open NativeRustcVm.Transcript (DecArea tstateBytes TStateAt)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

omit [Host] in
/-- Row `0` of the folded rows, as the list the postcondition reads. -/
theorem row0_at {d : DataMem} {sl : Array EW} {rows : Array (Array EW)}
    (hsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64) (hsl : sl.size = 6)
    {p : BitVec 64} (h : ElemsAt d p (Fr sl rows 6) 4096) :
    NativeRustcVm.EWsAt d p
      ((NativeRustcVm.KeccakGkr.openRows sl rows sl.size).getD 0 #[]).toList := by
  obtain ⟨-, hr6⟩ := openRows_shape hsz hrow (sl := sl) (t := 6) (by omega)
  have hl : ((NativeRustcVm.KeccakGkr.openRows sl rows 6).getD 0 #[]).toList.length = 64 := by
    rw [Array.length_toList]
    exact hr6 0 (by decide)
  rw [hsl]
  refine ElemsAt.ewsAt ?_
  rw [hl]
  intro i hi
  have := h i (by omega)
  rw [Fr_six hsz hrow hsl hi] at this
  show NativeRustcVm.EWAt d _
    (((NativeRustcVm.KeccakGkr.openRows sl rows 6).getD 0 #[]).toList.getD i 0)
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, ← Array.getD_eq_getD_getElem?]
  exact this

/-- **After the fold**: `b93` and the return with tag `1`. -/
theorem some_exit (hp : Placed code k) (h : KeccakOpenPre a s c m0) {s1 : TState}
    {sl : Array EW} {v : EW} (hrun : scRun s m0 = some ((sl, v), s1))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b93Offset))
    (hmid : Mid ⟨a, s1, sl, v⟩ m0 st.data)
    (hrw : ElemsAt st.data.dmem (rwA m0) (Fr sl (keccakSlotWeights m0.regs.X2.toNat c
      m0.regs.X6.toNat m0.regs.X7.toNat) 6) 4096) :
    Eventually (step1 Host.exe) (Goal a s c m0) st := by
  have ok := ok_of h
  have hn := ok.nums
  have hS := h.1
  have hA := pre_areas h
  have hN := hn.hN
  have hlt : spN m0 < 2 ^ 64 := m0.regs.SP.toBitVec.isLt
  have h2224 : 2224 ≤ keccakOpenStack := by rw [stack_eq]; decide
  obtain ⟨hmap, hnw, -⟩ := frame_ok hS h2224
  have hb := hmid.body
  have hro := Areas.ok hA (.inl (mem_out (m0 := m0)))
  have := hn.oW; have := hn.oS; have := hn.o_s; have := hn.sW; have := hn.o_r; have := hn.rW
  have hfbN := fb_toNat (m0 := m0) (by omega)
  have hwf : (Env.ofMachine st.data [(fbA m0, 2224), (oA m0, 24)]).WF := by
    refine Env.wf_of ⟨⟨Mapped.kept' hmap hb.kept, hnw⟩, ⟨Mapped.kept' hro.1 hb.kept, hro.2⟩,
      trivial⟩ (List.pairwise_cons.mpr ⟨fun e he ↦ ?_, List.pairwise_singleton _ _⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    show Apart (fbA m0) 2224 (oA m0) 24
    unfold Apart
    rw [hfbN]
    omega
  have hm : Match (Env.ofMachine st.data [(fbA m0, 2224), (oA m0, 24)]) outS st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS h2224 rfl, rfl, nofun, trivial⟩
      (by rw [hb.sp]; simp [Sym.eval]) trivial trivial trivial
      ⟨by
        show (Env.ofMachine st.data [(fbA m0, 2224), (oA m0, 24)]).load 0 32 8 =
          oA m0 + BitVec.ofInt 64 0
        rw [Sumcheck.load_word (env := Env.ofMachine st.data [(fbA m0, 2224), (oA m0, 24)])
          (r := 0) hmid.out, show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from rfl,
          NativeRustcVm.addr_add_zero], trivial⟩
  refine exec_at (b93_in_code.trans hp.1 (by simp [b93])) run_b93 hwf hpc hm
    fun s2 hm2 hpc2 ↦ ?_
  simp only [PcOk] at hpc2
  rw [label_at hp b95_in_code rfl] at hpc2
  have hb2 : Body m0 s2.data :=
    hb.write hS h2224 slots_le' (wsOff h) hm hm2 hwf rfl all_slots (by decide) fun p hw ↦
      ⟨_, mem_out, Sumcheck.Written.inRange (r := 1) (b := oA m0) (sz := 24) rfl hro.2
        (by decide +kernel) hw⟩
  have hso2 : SameOutside st.data.dmem s2.data.dmem (InRange (oA m0) 24) :=
    fun p hp ↦ hm2.sameOutside hwf p fun hw ↦ hp (Sumcheck.Written.inRange (r := 1) (b := oA m0)
      (sz := 24) rfl hro.2 (by decide +kernel) hw)
  have hval : NativeRustcVm.EWAt s2.data.dmem (oA m0 + BitVec.ofNat 64 8) v := by
    have := KeccakGkr.Match.ewAt_write hm2 (r := 1) (o := 8) rfl (by decide)
      (v0 := .load 0 16 8) (v1 := .load 0 24 8) (by decide +kernel) (by decide +kernel)
    rw [show (Sym.load 0 16 8).eval (Env.ofMachine st.data [(fbA m0, 2224), (oA m0, 24)]) =
        v.c0.toBitVec from Sumcheck.load_word
          (env := Env.ofMachine st.data [(fbA m0, 2224), (oA m0, 24)]) (r := 0) hmid.v0,
      show (Sym.load 0 24 8).eval (Env.ofMachine st.data [(fbA m0, 2224), (oA m0, 24)]) =
        v.c1.toBitVec from Sumcheck.load_word
          (env := Env.ofMachine st.data [(fbA m0, 2224), (oA m0, 24)]) (r := 0) hmid.v1,
      UInt64.ofBitVec_toBitVec, UInt64.ofBitVec_toBitVec] at this
    exact this
  have h19 : s2.data.regs.X19 = m0.regs.X0 := UInt64.toBitVec_inj.mp ((hm2.regs .X19 _ rfl).trans
    (Sumcheck.load_word (env := Env.ofMachine st.data [(fbA m0, 2224), (oA m0, 24)]) (r := 0)
      hmid.out))
  have h8 : s2.data.regs.X8 = 1 := UInt64.toBitVec_inj.mp (hm2.regs .X8 _ rfl)
  refine (tail_run hp h hpc2 hb2 h19).mono fun st' ⟨hpc', hsv, hwr, htag, hso3, hk3⟩ ↦ ?_
  have hso : SameOutside st.data.dmem st'.data.dmem (InRange (oA m0) 24) := fun p hp ↦
    (hso3 p fun h' ↦ hp (by unfold InRange at h' ⊢; omega)).trans (hso2 p hp)
  have hk : Kept st.data.dmem st'.data.dmem := fun p hp ↦ hk3 p (hm2.kept hwf p hp)
  have hout : ∀ q, InRange (oA m0) 24 q → (oA m0).toNat ≤ q.toNat ∧
      q.toNat < (oA m0).toNat + 24 := fun q hq ↦ (inRange_nat (by omega)).mp hq
  have hsl := hmid.sl_size
  obtain ⟨hsz, hrow⟩ := NativeVm.Math.Keccak.slotWeights_size m0.regs.X2.toNat c m0.regs.X6.toNat
    m0.regs.X7.toNat
  have hr := open_some (L := m0.regs.X2.toNat) (c := c) (f := m0.regs.X6.toNat)
    (n := m0.regs.X7.toNat) hrun
  refine ⟨hpc', ?_, fun sl' ws v' s' e ↦ ?_, hwr, hsv⟩
  · rw [hr]
    refine ⟨by rw [h8] at htag; exact htag, ?_⟩
    refine NativeRustcVm.BytesAt.of_sameOutside hval hso3 fun i hi hR ↦ ?_
    rw [NativeRustcVm.length_ewBytes] at hi
    rw [NativeRustcVm.addr_add_add, inRange_nat (x := oA m0) (n := 8) (by omega),
      toNat_add_ofNat' (a := oA m0) (i := 8 + i) (by omega)] at hR
    omega
  rw [hr] at e
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e
  refine ⟨?_, ?_, ?_⟩
  · refine NativeRustcVm.BytesAt.of_sameOutside hmid.slot hso fun i hi hR ↦ ?_
    rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hsl] at hi
    have := hout _ hR
    rw [toNat_add_ofNat' (a := slA m0) (i := i) (by omega)] at this
    omega
  · refine row0_at hsz hrow hsl (ElemsAt.keep hrw hso (fun q hq hR ↦ ?_) ?_)
    · rw [inRange_nat (x := rwA m0) (n := 16 * 4096) (by omega)] at hq
      have := hout q hR
      omega
    · show (rwA m0).toNat + 16 * 4096 ≤ 2 ^ 64
      omega
  · exact ts_keep hn hmid.ts hk hso fun q hq ↦ .inr (.inl (hout q hq))

end

end NativeRustcVmArm.KeccakGkr.KeccakOpen
