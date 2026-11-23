module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.Exit

/-!
# `keccak_open`: returning the folded row

The saved sumcheck value is written into the output, then the tag and epilogue return.
The slot point, folded rows and transcript are preserved by both output writes.
-/

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.KeccakOpen
open LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeRustcVm.Transcript (off off_zero off_off off_add toNat_off inRange_iff' Mapped.keeps
  bytesAt_congr DecArea tstateBytes TStateAt Touch)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

theorem some_exit (hp : Placed code k) (h : PreOk a s c m0) {s1 : TState}
    {sl : Array EW} {v : EW}
    (hrun : (sumcheckPlain (openValue m0) 3 qkeccakSlotBits).run s = some ((sl, v), s1))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b93Offset))
    (hm : Mid ⟨a, s1, sl, v⟩ m0 8 st.data)
    (hrw : ElemsAt st.data.dmem (rwA m0) (Fr sl (keccakSlotWeights (reg m0 .rdx).toNat c
      (openFirst m0).toNat (openCount m0).toNat) 6) 4096) :
    Eventually (step1 Host.exe) (Goal a s c m0) st := by
  have hn := nums h
  have := hn.r1; have := hn.r2; have := hn.o; have := hn.t; have := hn.s; have := hn.w
  have := hn.a; have := hn.os; have := hn.ow; have := hn.ot; have := hn.oa
  have hwf := wf_out h hm.fr.kept
  have hmatch : Match (frameEnv m0 st.data 2208 [(oA m0, 24)] (fun _ ↦ 0) 0) outS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hm.fr.rsp_eval, trivial⟩ trivial trivial ⟨by
      show (frameEnv m0 st.data 2208 [(oA m0, 24)] (fun _ ↦ 0) 0).load 0 64 8 =
        oA m0 + BitVec.ofInt 64 0
      rw [load_of_wordAt hm.out, UInt64.toBitVec_ofBitVec, ofInt0, BitVec.add_zero], trivial⟩
  refine exec_at (infix_of b93_in_code (by simp [b93]) hp) x93 hwf nofun hpc hmatch
    fun st2 hm2 hpc2 ↦ ?_
  have hf2 := hm.fr.of_block hwf hm2 f93.2.1 slots_le'
  have hso2 : NativeRustcVm.SameOutside st.data.dmem st2.data.dmem
      (NativeRustcVm.InRange (oA m0) 24) := by
    have ht := sameOutside_touch hwf hm2 (r := 1) (b := oA m0) (N := 24)
      (lo := 0) (hi := 24) rfl (by decide) (by
        intro w hw
        rw [f93.2.2.1] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> exact ⟨rfl, by decide⟩)
    exact fun q hq ↦ ht q fun htq ↦ hq (inRange_of_touch (by omega) htq)
  have hs2 : NativeRustcVm.SameOutside m0.dmem st2.data.dmem (Out m0) := fun q hq ↦
    (hso2 q fun hr ↦ hq ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hr⟩).trans (hm.same q hq)
  have hv2 : NativeRustcVm.EWAt st2.data.dmem (off (oA m0) 8) v := by
    have he := Match.ewAt_write hm2 (r := 1) (o := 8) (v0 := .load 0 80 8)
      (v1 := .load 0 72 8) rfl (by decide)
      (by rw [f93.2.2.1]; decide +kernel) (by rw [f93.2.2.1]; decide +kernel)
    change NativeRustcVm.EWAt _ _ ⟨UInt64.ofBitVec ((frameEnv m0 st.data 2208
      [(oA m0, 24)] (fun _ ↦ 0) 0).load 0 80 8), UInt64.ofBitVec ((frameEnv m0 st.data 2208
      [(oA m0, 24)] (fun _ ↦ 0) 0).load 0 72 8)⟩ at he
    rw [load_of_wordAt hm.v0, load_of_wordAt hm.v1, UInt64.ofBitVec_toBitVec,
      UInt64.ofBitVec_toBitVec] at he
    exact he
  have hbx : reg st2.data .rbx = oA m0 := by
    rw [show reg st2.data .rbx = _ from hm2.regs .rbx _ f93.2.2.2.1]
    change (frameEnv m0 st.data 2208 [(oA m0, 24)] (fun _ ↦ 0) 0).load 0 64 8 = _
    rw [load_of_wordAt hm.out, UInt64.toBitVec_ofBitVec]
  have hax : reg st2.data .rax = 1#64 := hm2.regs .rax _ f93.2.2.2.2
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b95Offset) := by
    simp only [PcOk] at hpc2
    exact hpc2.trans (label_of_infix hp b95_in_code rfl)
  refine (tail_run hp h hpc2' hf2 hs2 hbx).mono fun st' ⟨hpc', hrsp, hsv, hwr, htag, hso3, hk3⟩ ↦ ?_
  have hso : NativeRustcVm.SameOutside st.data.dmem st'.data.dmem
      (NativeRustcVm.InRange (oA m0) 24) := fun q hq ↦
    (hso3 q fun hq' ↦ hq (inRange_mono hq' (by decide))).trans (hso2 q hq)
  have hk : Kept st.data.dmem st'.data.dmem := kept_trans (hm2.kept hwf) hk3
  have hout : ∀ q, NativeRustcVm.InRange (oA m0) 24 q →
      (oA m0).toNat ≤ q.toNat ∧ q.toNat < (oA m0).toNat + 24 :=
    fun q hq ↦ (inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)).mp hq
  have hr := open_some (L := (reg m0 .rdx).toNat) (c := c) (f := (openFirst m0).toNat)
    (n := (openCount m0).toNat) hrun
  refine ⟨hpc', hrsp, ?_, ?_, hwr, hsv⟩
  · rw [hr]
    refine ⟨by rw [hax] at htag; exact htag, ?_⟩
    refine bytesAt_congr hv2 fun i hi ↦ hso3 _ fun hq ↦ ?_
    rw [NativeRustcVm.length_ewBytes] at hi
    change NativeRustcVm.InRange (oA m0) 8 (off (oA m0) 8 + BitVec.ofNat 64 i) at hq
    rw [off_add, inRange_iff' (by unfold NativeRustcVm.NoWrap; omega),
      toNat_off (by omega)] at hq
    omega
  · intro sl' ws v' s' he
    rw [hr] at he
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := he
    refine ⟨?_, ?_, ?_⟩
    · refine bytesAt_congr hm.slot fun i hi ↦ hso _ fun hq ↦ ?_
      rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hm.sl_size] at hi
      have hq' := hout _ hq
      rw [show slA m0 + BitVec.ofNat 64 i = off (slA m0) i from rfl,
        toNat_off (by omega)] at hq'
      omega
    · obtain ⟨hsz, hrow⟩ := NativeVm.Math.Keccak.slotWeights_size (reg m0 .rdx).toNat c
        (openFirst m0).toNat (openCount m0).toNat
      refine row0_at hsz hrow hm.sl_size (hrw.keep hso (fun q hq ho ↦ ?_) (by
        unfold NativeRustcVm.NoWrap; omega))
      rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)] at hq
      have := hout q ho
      omega
    · refine hm.ts.frame hk (fun q hq ↦ ?_) hso
      have := hout q hq
      constructor
      · rw [show tstateBytes = 760 from rfl,
          inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)]
        omega
      · change ¬ NativeRustcVm.InRange a.words (8 * a.len) q
        rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)]
        omega

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
