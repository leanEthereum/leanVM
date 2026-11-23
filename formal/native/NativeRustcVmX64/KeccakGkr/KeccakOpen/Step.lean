module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.Known
public import NativeRustcVmX64.Code.Vm.KeccakOpen
public import NativeRustcVmX64.Code.Vm.Memcpy.Names

/-!
# `keccak_open`: a block around the fold, a row's copy (x86-64)

A block from `pS ks` checked by `blkOk` (`blk_run`): the state around the fold, the known
registers and saved words after it, memory changed only in the frame below `64`. A block calling
`memcpy` checked by `mOk` and the call (`copy_run`): 1024 bytes of the rows copied into a row
buffer (`elems_copy`).
-/

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.KeccakOpen
open NativeRustcVm (Region InAny)
open NativeRustcVm.Transcript (off off_zero off_off off_add toNat_off inRange_iff' Mapped.keeps
  bytesAt_congr inRange_off_self DecArea tstateBytes TStateAt Touch)

public section

theorem wfK_of_regsOk {kl : List (Sym × Sym)} {S : SState} {ks : List (Reg64 × Sym)}
    (h : regsOk kl S ks = true) : wfK ks = true := by
  refine List.all_eq_true.mpr fun p hp ↦ ?_
  have := List.all_eq_true.mp h p hp
  simp only [Bool.and_eq_true] at this ⊢
  exact this.1

theorem wsB_of_wordsOk {kl : List (Sym × Sym)} {S : SState} {ws ws' : List (Nat × Sym)}
    (h : wordsOk kl S ws ws' = true) :
    ws'.all (fun p ↦ decide (16 ≤ p.1) && decide (p.1 + 8 ≤ 64)) = true := by
  refine List.all_eq_true.mpr fun p hp ↦ ?_
  have := List.all_eq_true.mp h p hp
  simp only [wordOk, Bool.and_eq_true] at this ⊢
  exact ⟨this.1.1.2, this.1.2⟩

theorem wfW_of_wordsOk {kl : List (Sym × Sym)} {S : SState} {ws ws' : List (Nat × Sym)}
    (h : wordsOk kl S ws ws' = true) : wfW ws' = true := by
  refine List.all_eq_true.mpr fun p hp ↦ ?_
  have := List.all_eq_true.mp h p hp
  simp only [wordOk, Bool.and_eq_true] at this
  exact this.1.1.1

/-- **Elements copied**: `memcpy`'s bytes of `n` elements are the elements. -/
theorem elems_copy {d d' : DataMem} {src dst : BitVec 64} {f : Nat → EW} {n : Nat}
    (hs : ElemsAt d src f n) (hb : NativeRustcVm.BytesAt d' dst (bytesOf d src (16 * n))) :
    ElemsAt d' dst f n := by
  intro i hi j hj
  rw [NativeRustcVm.length_ewBytes] at hj
  have h1 := hb (16 * i + j) (by rw [length_bytesOf]; omega)
  have h2 := hs i hi j (by rw [NativeRustcVm.length_ewBytes]; exact hj)
  rw [off_add] at h2 ⊢
  rw [show dst + BitVec.ofNat 64 (16 * i + j) = off dst (16 * i + j) from rfl] at h1
  rw [h1]
  simp only [NativeRustcX64.bytesOf, List.getElem_map, List.getElem_range]
  rw [show src + BitVec.ofNat 64 (16 * i + j) = off src (16 * i + j) from rfl, h2]
  rfl

variable [Host] {a : DecArea} {s : TState} {c : KeccakClaimW} {cx : Cx} {m0 : MachineData}
  {vars : Nat → BitVec 64} {ks ks' : List (Reg64 × Sym)} {ws ws' : List (Nat × Sym)}

/-- **A block around the fold.** -/
theorem blk_run {k : Nat} (hp : Placed code k) (h : PreOk a s c m0) (hA : cx.a = a)
    {t : Nat} (hv : VarsOk cx t vars) (hwk : wfK ks = true) (hws : wfW ws = true)
    {b : List Directive} {kb : Nat} (hin : b.IsInfixAt code kb) (hne : b ≠ [])
    {S : SState} {x : Exit} (hx : exec b (pS ks) = some (S, x))
    {o' : Nat} (hok : blkOk o' t ws S ks' ws' = true)
    {ret : BitVec 64} (hret : ∀ l, x = .call l → ret = (Host.addrOf (k + kb + b.length)).toBitVec)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + kb))
    (hm : Mid cx m0 8 st.data) (hk : KAt m0 vars ks st.data) (hw : Words m0 vars ws st.data)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState,
      PcOk (E m0 st.data vars ret) x (Host.addrOf (k + kb + b.length)) st' →
      Match (E m0 st.data vars ret) S st'.data → Mid cx m0 o' st'.data →
      KAt m0 vars ks' st'.data → Words m0 vars ws' st'.data →
      NativeRustcVm.SameOutside st.data.dmem st'.data.dmem
        (Touch (fbA m0) 2216 (fun j ↦ 0 ≤ j ∧ j < 64)) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  simp only [blkOk, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨hmid, hlow⟩, hregs⟩, hwds⟩ := hok
  have hwf : (E m0 st.data vars ret).WF := wf_fold h hm.fr.kept
  have hkl := kl_ok h hm hv hw hws (ret := ret)
  refine exec_at (infix_of hin hne hp) hx hwf (fun l hl ↦ by rw [hret l hl, Nat.add_assoc]; rfl)
    (by rw [hpc]) (match_pS h hm hk hwk) fun st' hm' hpc' ↦ ?_
  have hf' := Frame.of_block hm.fr hwf hm' hmid slots_le'
  have hlowS : ∀ w ∈ S.mem, w.r = 0 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 64 := fun w hw' ↦ by
    have := List.all_eq_true.mp hlow w hw'
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact ⟨this.1, Nat.zero_le _, this.2⟩
  have hso := sameOutside_touch hwf hm' (r := 0) (b := fbA m0) (N := 2216) rfl (by decide) hlowS
  have hmid' := Mid.keep h hm hf' (hm'.kept hwf) hso (fun q hq ↦ touch64_safe h hq) hA
  exact cont st' hpc' hm' hmid'
    (KAt.after hm' hkl rfl rfl hregs) (Words.after h hwf hm' hkl hlow hw hwds) hso

/-- **A row copied** into the frame's buffer at `dst`: a block calling `memcpy` with row `r` of
the rows. -/
theorem copy_run {k : Nat} (hp : Placed code k)
    (hmemcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) (h : PreOk a s c m0)
    (hA : cx.a = a) {t : Nat} (hv : VarsOk cx t vars) (hwk : wfK ks = true) (hws : wfW ws = true)
    {b : List Directive} {kb : Nat} (hin : b.IsInfixAt code kb) (hne : b ≠ [])
    {S : SState} (hx : exec b (pS ks) = some (S, .call NativeRustcVmX64.Vm.Memcpy.entryLabel))
    {dst : Nat} {src : Sym} (hok : mOk dst src t ws S ks' ws' = true)
    (hdst : 112 ≤ dst ∧ dst + 1024 ≤ 2160) {r : Nat} (hr : r < 64)
    (hsv : src.eval (envK m0 vars) = rwA m0 + BitVec.ofNat 64 (1024 * r))
    {G : Nat → EW} {st : MachineState} (hpc : st.pc = Host.addrOf (k + kb))
    (hm : Mid cx m0 8 st.data) (hk : KAt m0 vars ks st.data) (hw : Words m0 vars ws st.data)
    (hrows : ElemsAt st.data.dmem (rwA m0) G 4096) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + kb + b.length) ∧
      Mid cx m0 8 st'.data ∧ KAt m0 vars ks' st'.data ∧ Words m0 vars ws' st'.data ∧
      ElemsAt st'.data.dmem (rwA m0) G 4096 ∧
      ElemsAt st'.data.dmem (off (fbA m0) dst) (fun z ↦ G (64 * r + z)) 64 ∧
      NativeRustcVm.SameOutside st.data.dmem st'.data.dmem (fun q ↦
        Touch (fbA m0) 2216 (fun j ↦ 0 ≤ j ∧ j < 64) q ∨
          NativeRustcVm.InRange (off (fbA m0) dst) 1024 q)) st := by
  have hn := nums h
  have := hn.r1; have := hn.r2; have := hn.w; have := hn.sw
  have hfb : (stackBelow m0 2208).toNat = _ := fbA_toNat h
  have hfb2 := fbA_toNat h
  unfold mOk at hok
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨hblk, hdi⟩, hdx⟩, hsst⟩, hsi⟩ := hok
  have hwk' := wfK_of_regsOk (by simp only [blkOk, Bool.and_eq_true] at hblk; exact hblk.1.2)
  have hwsB := wsB_of_wordsOk (by simp only [blkOk, Bool.and_eq_true] at hblk; exact hblk.2)
  refine blk_run hp h hA hv hwk hws hin hne hx hblk (ret := (Host.addrOf (k + kb + b.length)).toBitVec)
    (fun _ _ ↦ rfl) hpc hm hk hw fun st1 hpc1 hm1 hmid1 hk1 hw1 hso1 ↦ ?_
  have hkl := kl_ok h hm hv hw hws (ret := (Host.addrOf (k + kb + b.length)).toBitVec)
  -- the arguments
  have hrdi : reg st1.data .rdi = off (fbA m0) dst := (hm1.regs .rdi _ hdi).trans (eval_ptr0 dst)
  have hrdx : (reg st1.data .rdx).toNat = 1024 := by
    rw [show reg st1.data .rdx = _ from hm1.regs .rdx _ hdx]; rfl
  have hrsi : reg st1.data .rsi = off (rwA m0) (1024 * r) := by
    cases hrs : S.reg .rsi with
    | none => rw [hrs] at hsi; cases hsi
    | some e =>
      rw [hrs, Option.map_some, Option.some.injEq] at hsi
      rw [show reg st1.data .rsi = _ from hm1.regs .rsi e hrs, ← subst_eval hkl e, hsi,
        ← eval_K st.data vars _ hsst, hsv]
  have hsp1 : rspOf st1.data = stackBelow m0 2208 := by rw [hmid1.fr.sp, off_zero]
  have hrm : NativeRustcVm.Mapped m0.dmem (rwA m0) 65536 :=
    (Areas.ok h.areas (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.head _)))))).1
  have hfm := frame_mapped h.st (F := 2208) (by rw [stack_eq]; decide)
  have hdn : (off (fbA m0) dst).toNat = (rspOf m0).toNat - 2208 + dst := fb_off h (by omega)
  have hsn : (off (rwA m0) (1024 * r)).toNat = (rwA m0).toNat + 1024 * r := toNat_off (by omega)
  have hpre : MemcpyPre st1.data := by
    simp only [MemcpyPre]
    rw [hrdi, hrsi, hrdx]
    refine ⟨stackOk_callee h.st hmid1.fr.kept hsp1 (by rw [stack_eq]; omega),
      Mapped.keeps (mapped_off hfm (by omega)) hmid1.fr.kept,
      Mapped.keeps (mapped_off hrm (by omega)) hmid1.fr.kept, ?_, ?_, ?_, ?_⟩
    · show _ + _ ≤ _; omega
    · show _ + _ ≤ _; omega
    · show _ + _ ≤ _ ∨ _ + _ ≤ _; omega
    · show _ + _ ≤ _ ∨ _ + _ ≤ _; rw [hsp1, hfb]; omega
  refine call_then hpc1 hmemcpy hpre fun st2 hpc2 hrsp2 hpost ↦ ?_
  simp only [MemcpyPost] at hpost
  obtain ⟨-, hb2, hso2, hsv2⟩ := hpost
  rw [hrdi, hrsi, hrdx] at hb2
  rw [hrdi, hrdx] at hso2
  have hin2 : ∀ q, NativeRustcVm.InRange (off (fbA m0) dst) 1024 q →
      (rspOf m0).toNat - 2208 + dst ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - 2208 + dst + 1024 :=
    fun q hq ↦ by
      rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), hdn] at hq; exact hq
  have hf2 : Frame m0 2208 slots 8 st2.data :=
    Frame.call_at hmid1.fr hsv2 hrsp2 hso2 (fun p hp i hi hq ↦ by
        have := slots_le p hp
        have := hin2 _ hq
        rw [fb_off h (by omega)] at this
        omega)
      (fun j hj hq ↦ by
        have := hin2 _ hq
        rw [fb_off h (by omega)] at this
        omega)
  have hmid2 := Mid.keep h hmid1 hf2 hsv2.2 hso2 (fun q hq ↦ by
    have := hin2 q hq
    unfold Safe SafeN
    omega) hA
  have hrows1 : ElemsAt st1.data.dmem (rwA m0) G 4096 :=
    hrows.keep hso1 (fun q hq ht ↦ by
      obtain ⟨j, hj, hj', rfl⟩ := ht
      rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega),
        fb_off h (by omega)] at hq
      omega) (by unfold NativeRustcVm.NoWrap; omega)
  have hchunk : ElemsAt st1.data.dmem (off (rwA m0) (1024 * r)) (fun z ↦ G (64 * r + z)) 64 :=
    fun z hz ↦ by
      rw [off_off, show 1024 * r + 16 * z = 16 * (64 * r + z) by omega]
      exact hrows1 _ (by omega)
  refine .done _ ⟨hpc2, hmid2, KAt.call hk1 hwk' hsv2, Words.keep h hw1 hwsB hso2 fun q hq ↦ by
    have := hin2 q hq; omega, ?_, elems_copy hchunk hb2, ?_⟩
  · exact hrows1.keep hso2 (fun q hq hq' ↦ by
      have := hin2 q hq'
      rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)] at hq
      omega) (by unfold NativeRustcVm.NoWrap; omega)
  · intro q hq
    rw [hso2 q fun h' ↦ hq (.inr h'), hso1 q fun h' ↦ hq (.inl h')]

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
