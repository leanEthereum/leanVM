module

public import NativeRustcVmX64.Top.Seed.Stage1
public import NativeRustcVmX64.Code.Vm.KeccakF.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names

/-!
# `seed` from `memset` on (x86-64)

`stage2`: from `S1`, `b2` copies the public input to the frame's bytes 48 to 79, so that its bytes
16 to 215 hold the state `Model.seed` permutes (`seed_state`); `keccak_f` permutes it in place,
`b3` and `memcpy` copy it to the output, `b4` restores the registers and returns.
-/

namespace NativeRustcVmX64.Top.Seed

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Seed NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript NativeRustcVmX64.Top NativeVm.Model LeanVM.Semantics LeanVM.Parameters

public section

/-- The state `seed` permutes: the IV, the public input, zeros. -/
theorem seed_state (iv : LeanVM.Protocol.Digest) (P : Vector UInt64 4) :
    (Vector.ofFn (n := 25) fun i ↦
      if h : i.val < 4 then iv[i.val] else if h' : i.val < 8 then P[i.val - 4] else 0).toList =
      iv.toList ++ P.toList ++ List.replicate 17 0 := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [Vector.toList_ofFn, List.getElem_ofFn]
  have hl : (iv.toList ++ P.toList).length = 8 := by simp
  by_cases ha : i < 4
  · simp only [ha, ↓reduceDIte]
    rw [List.getElem_append_left (by rw [hl]; omega), List.getElem_append_left (by simp; omega)]
    simp
  · by_cases hb : i < 8
    · simp only [ha, hb, ↓reduceDIte]
      rw [List.getElem_append_left (by rw [hl]; omega),
        List.getElem_append_right (by simp; omega)]
      simp
    · simp only [ha, hb, ↓reduceDIte]
      rw [List.getElem_append_right (by rw [hl]; omega), List.getElem_replicate]

/-- Zero bytes are zero words. -/
theorem wordsAt_zeros {d : DataMem} {a : BitVec 64} (k : Nat)
    (h : NativeRustcVm.BytesAt d a (List.replicate (8 * k) 0)) :
    NativeRustcVm.WordsAt d a (List.replicate k 0) := by
  have e : ∀ k, (List.replicate k (0 : UInt64)).flatMap NativeRustcVm.wordBytes =
      List.replicate (8 * k) 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.replicate_succ, List.flatMap_cons, ih, show 8 * (k + 1) = 8 + 8 * k by omega,
        ← List.replicate_append_replicate]
      rfl
  unfold NativeRustcVm.WordsAt
  rw [e]
  exact h

variable [Host] {k : Nat}

/-- **`seed` from `memset` on.** -/
theorem stage2 (hp : Placed code k)
    (hkf : Spec (Labels.label NativeRustcVmX64.Vm.KeccakF.entryLabel) KeccakFPre KeccakFPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) {m0 : MachineData}
    (hpre : SeedPre m0) {st4 : MachineState} (hpc4 : st4.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Seed.b2Offset))
    (hS1 : S1 m0 st4.data) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
      SeedPost m0 st.data) st4 := by
  obtain ⟨hst, hrc, -, ⟨-, -⟩, ⟨hpubM, hpubN⟩, ⟨houtM, houtN⟩, hdP, hdO, -, hgot⟩ := hpre
  obtain ⟨hf4, hs4, hiv4, hz4, hrbx4, hr144, hr154⟩ := hS1
  set out := reg m0 .rdi with hout
  set pub := reg m0 .rcx with hpub
  set a := off (fb m0) 16 with ha
  have hss : seedStack = 1008 := rfl
  have hkf' : keccakFStack = 480 := rfl
  have hn : seedStack ≤ (rspOf m0).toNat := hst.1
  have h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hst.2.1
  have hfnw := frame_noWrap (F := 240) hst (by decide)
  have hBn : (fb m0).toNat = (rspOf m0).toNat - 240 := stackBelow_toNat (by omega)
  have hoff : ∀ j, j < 248 → (off (fb m0) j).toNat = (rspOf m0).toNat - 240 + j := fun j hj ↦ by
    rw [toNat_off (by omega), hBn]
  have hsbn : (stackBelow m0 seedStack).toNat = (rspOf m0).toNat - 1008 :=
    stackBelow_toNat (by omega)
  have hpubN' : pub.toNat + 32 ≤ 2 ^ 64 := hpubN
  have houtN' : out.toNat + 200 ≤ 2 ^ 64 := houtN
  have hPA := apart_of_pair hdP
  have hOA := apart_of_pair hdO
  simp only [stackR] at hPA hOA
  unfold NativeRustcVm.Apart at hPA hOA
  rw [hsbn, hss] at hPA hOA
  have hrcN := hrc.2.1
  have hrcA := hrc.2.2
  unfold NativeRustcVm.Apart at hrcA
  unfold NativeRustcVm.NoWrap at hrcN
  rw [hsbn, hss] at hrcA
  have ha_n : a.toNat = (rspOf m0).toNat - 224 := by rw [ha, hoff 16 (by decide)]; omega
  have hFm : ∀ d : MachineData, Kept m0.dmem d.dmem →
      NativeRustcVm.Mapped d.dmem (fb m0) (240 + 8) :=
    fun d hk ↦ Mapped.keeps (frame_mapped hst (by decide)) hk
  have hstk : ∀ q, (rspOf m0).toNat - 1008 ≤ q.toNat → q.toNat < (rspOf m0).toNat →
      NativeRustcVm.InRange (stackBelow m0 seedStack) seedStack q := by
    intro q h1 h2
    rw [inR (by unfold NativeRustcVm.NoWrap; omega), hsbn, hss]
    omega
  -- `b2`: the public input to the frame, `call keccak_f`.
  have hwf4 := frame_wf (m0 := m0) (d := st4.data) (F := 240) (rest := [(pub, 32)])
    (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.Seed.b2Offset + b2.length)).toBitVec)
    ⟨hFm _ hf4.kept, hfnw⟩
    (fun x hx ↦ by
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨Mapped.keeps hpubM hf4.kept, hpubN⟩)
    (List.pairwise_pair.mpr (by unfold NativeRustcVm.Apart; dsimp only; rw [hBn]; omega))
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf4 (fun _ _ ↦ rfl)
    hpc4
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf4.rsp_eval, known_ptr rfl hr154, trivial⟩ trivial
      trivial trivial) fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hmid5, hw5, hwr5, hrdi5, hrbx5, hr145⟩ := after_eq run_b2 ▸ ok_b2
  have hf5 : Frame m0 240 slots 0 st5.data := Frame.of_block hf4 hwf4 hm5 hmid5 slots_le
  have hsp5 : rspOf st5.data = fb m0 := by rw [hf5.sp, off_zero]
  have hs5 : NativeRustcVm.SameOutside st4.data.dmem st5.data.dmem
      (fun q ↦ Touch (fb m0) 248 (fun j ↦ j < 8 ∨ 48 ≤ j ∧ j < 80) q) :=
    sameOutside_W hwf4 hm5 (r := 0) rfl fun w hw ↦ by
      obtain ⟨hr, hb⟩ := hw5 w hw
      exact ⟨hr, by omega, fun j h1 h2 ↦ by omega⟩
  have hs5' : ∀ q, Touch (fb m0) 248 (fun j ↦ j < 8 ∨ 48 ≤ j ∧ j < 80) q →
      (fb m0).toNat ≤ q.toNat ∧ q.toNat < (fb m0).toNat + 80 := by
    rintro q ⟨j, hj, hW, rfl⟩
    rw [hoff j hj]
    omega
  have eRdi5 : reg st5.data .rdi = a := (hm5.regs .rdi _ hrdi5).trans hr144
  have eRbx5 : reg st5.data .rbx = out := (hm5.regs .rbx _ hrbx5).trans hrbx4
  have eR145 : reg st5.data .r14 = a := (hm5.regs .r14 _ hr145).trans hr144
  -- The state in the frame.
  have hP4 : ∀ P : Vector UInt64 4, NativeRustcVm.WordsAt m0.dmem pub P.toList →
      NativeRustcVm.WordsAt st4.data.dmem pub P.toList := fun P hP ↦
    hP.of_sameOutside hs4 fun i hi h ↦ by
      rw [NativeRustcVm.length_wordsBytes, Vector.length_toList] at hi
      rw [inR (by unfold NativeRustcVm.NoWrap; omega), hsbn, hss,
        NativeRustcVm.toNat_add_ofNat (by omega)] at h
      omega
  have hst5 : ∀ w : List UInt64, w.length = (reg m0 .rdx).toNat →
      NativeRustcVm.WordsAt m0.dmem (reg m0 .rsi) w → ∀ P : Vector UInt64 4,
      NativeRustcVm.WordsAt m0.dmem pub P.toList →
      NativeRustcVm.WordsAt st5.data.dmem a
        (Vector.ofFn (n := 25) fun i ↦ if h : i.val < 4 then (fiatShamirIv w.toArray)[i.val]
          else if h' : i.val < 8 then P[i.val - 4] else 0).toList := by
    intro w hw hbc P hP
    rw [seed_state, NativeRustcVm.wordsAt_append_iff, NativeRustcVm.wordsAt_append_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have hl : ∀ j, j < 16 + (List.flatMap NativeRustcVm.wordBytes
          (fiatShamirIv w.toArray).toList).length → j < 48 := fun j h ↦ by
        rw [NativeRustcVm.length_wordsBytes, Vector.length_toList] at h; omega
      refine keep_off (hiv4 w hw hbc) hs5 fun j h1 h2 ↦ not_touch
        (by unfold NativeRustcVm.NoWrap; omega) ?_ ?_
      · have := hl j h2; omega
      · have := hl j h2; omega
    · simp only [Vector.length_toList, ha, off_add]
      refine wordsAt_iff.mpr fun q hq ↦ ?_
      have hq4 : q < 4 := by simpa using hq
      have h := wordAt_write hm5 (r := 0) (o := 48 + 8 * q) rfl (by omega)
        (hwr5 q hq4)
      have hl : (Sym.load 1 (8 * q) 8).eval
          (frameEnv m0 st4.data 240 [(pub, 32)] (fun _ ↦ 0)
            (Host.addrOf (k + NativeRustcVmX64.Vm.Seed.b2Offset + b2.length)).toBitVec) = P.toList[q].toBitVec :=
        load_ofMachine (r := 1) rfl ((wordsAt_iff.mp (hP4 P hP)) q hq)
      rw [hl, UInt64.ofBitVec_toBitVec] at h
      have h' : ∀ o, o = 48 + 8 * q → NativeRustcVm.WordAt st5.data.dmem (off (fb m0) o)
          P.toList[q] := fun o ho ↦ ho ▸ h
      rw [off_off]
      exact h' _ (by omega)
    · simp only [List.length_append, Vector.length_toList, ha, off_add]
      refine wordsAt_zeros 17 (keep_off hz4 hs5 fun j h1 h2 ↦ ?_)
      simp only [List.length_replicate] at h2
      exact not_touch (by unfold NativeRustcVm.NoWrap; omega) (by omega) (by omega)
  -- `keccak_f`, in place.
  have hrc5 : ∀ i < 192, st5.data.dmem.get? (rcAddr + BitVec.ofNat 64 i) =
      m0.dmem.get? (rcAddr + BitVec.ofNat 64 i) := by
    intro i hi
    have hq : (rcAddr + BitVec.ofNat 64 i).toNat = rcAddr.toNat + i :=
      NativeRustcVm.toNat_add_ofNat (by omega)
    refine (hs5 _ fun h ↦ ?_).trans (hs4 _ fun h ↦ ?_)
    · have := hs5' _ h; omega
    · rw [inR (by unfold NativeRustcVm.NoWrap; omega), hsbn, hss] at h; omega
  have hg4 := got_keep hst hgot hs4 (fun q h ↦ by
    rw [inR (by unfold NativeRustcVm.NoWrap; omega), hsbn, hss] at h
    rw [hsbn]
    omega)
  have hg5 := got_keep hst hgot hs5 (fun q h ↦ by
    have hh := hs5' q h
    rw [hsbn]
    omega)
  have hpre5 : KeccakFPre st5.data := by
    unfold KeccakFPre
    simp only [eRdi5]
    refine ⟨stackOk_callee hst hf5.kept hsp5 (by omega),
      RcAt.callee hrc hrc5 hsp5 hn (by omega),
      mapped_off (hFm _ hf5.kept) (by decide), by unfold NativeRustcX64.NoWrap; omega, ?_, ?_, ?_⟩
    · rw [stackBelow_callee hsp5 (by omega)]
      unfold NativeRustcX64.Apart
      rw [stackBelow_toNat (by omega)]
      omega
    · unfold NativeRustcX64.Apart
      omega
    · have hg := got_leaf (n := keccakFStack) (bytes := 200)
        hst hgot (by simp) hsp5 (by decide) (by decide)
        (fun l hl i hi ↦ (hg5 l hl i hi).trans (hg4 l hl i hi))
      exact hg.symbols (show ["memcpy"].Sublist ["memcpy", "memset"] by simp)
  refine call_then hpc5 hkf hpre5 fun st6 hpc6 hrsp6 hpost6 ↦ ?_
  obtain ⟨hkf6, hs6, hsv6⟩ := hpost6
  simp only [eRdi5] at hkf6 hs6
  have hR6 : ∀ q, (NativeRustcVm.InRange a 200 q ∨
      NativeRustcVm.InRange (stackBelow st5.data keccakFStack) keccakFStack q) →
      (rspOf m0).toNat - 1008 ≤ q.toNat ∧ q.toNat < (fb m0).toNat + 216 := by
    rintro q (h | h)
    · rw [inR (by unfold NativeRustcVm.NoWrap; omega)] at h
      omega
    · have := callee_nat hsp5 (by omega) h
      omega
  have hf6 : Frame m0 240 slots 8 st6.data :=
    Frame.call_low hf5 hsv6 hrsp6 hs6 (fun q h ↦ Or.inl (hR6 q h).2) slots_ge (by decide) hfnw
      slots_le
  -- `b3`: `call memcpy`.
  have hg6 := got_keep hst hgot hs6 (fun q h ↦ by
    have hh := hR6 q h
    rw [hsbn]
    omega)
  have hwf6 := frame_wf (m0 := m0) (d := st6.data) (F := 240)
    (rest := [(gotAddr "memcpy", 8)]) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.Seed.b3Offset + b3.length)).toBitVec)
    ⟨hFm _ hf6.kept, hfnw⟩
    (by
      intro x hx
      obtain rfl := List.mem_singleton.mp hx
      exact ⟨Mapped.keeps (hgot.mapped (by simp)) hf6.kept, (hgot.1 "memcpy" (by simp)).2.1⟩)
    (List.pairwise_pair.mpr (got_frame_apart hst hgot (by simp)).symm)
  have hm6 : Match
      (frameEnv m0 st6.data 240 [(gotAddr "memcpy", 8)] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.Seed.b3Offset + b3.length)).toBitVec)
      (gotS "memcpy") st6.data := by
    apply Match.withKnownBytes
    · exact match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf6.rsp_eval, trivial⟩ trivial trivial
        ⟨(BitVec.add_zero _).symm, trivial⟩
    · intro i hi
      have hb := (hg6 "memcpy" (by simp) i hi).trans
        ((hg5 "memcpy" (by simp) i hi).trans
          ((hg4 "memcpy" (by simp) i hi).trans (hgot.byte (by simp) hi)))
      simpa [frameEnv, Env.base, Sym.eval] using hb
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf6 (fun _ _ ↦ rfl)
    (hpc6.trans (by rw [show k + NativeRustcVmX64.Vm.Seed.b2Offset + b2.length = k + NativeRustcVmX64.Vm.Seed.b3Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.Seed.b2_next]]))
    hm6
    fun st7 hm7 hpc7 ↦ ?_
  obtain ⟨hmid7, hw7, hrdi7, hrsi7, hrdx7⟩ := after_eq run_b3 ▸ ok_b3
  have hf7 : Frame m0 240 slots 0 st7.data := Frame.of_block hf6 hwf6 hm7 hmid7 slots_le
  have hsp7 : rspOf st7.data = fb m0 := by rw [hf7.sp, off_zero]
  have hs7 : NativeRustcVm.SameOutside st6.data.dmem st7.data.dmem
      (NativeRustcVm.InRange (fb m0) 8) :=
    sameOutside_low hwf6 hm7 (r := 0) rfl (by decide) hw7
  have eRdi7 : reg st7.data .rdi = out :=
    (hm7.regs .rdi _ hrdi7).trans ((hsv6.1 .rbx rfl).trans eRbx5)
  have eRsi7 : reg st7.data .rsi = a :=
    (hm7.regs .rsi _ hrsi7).trans ((hsv6.1 .r14 rfl).trans eR145)
  have eRdx7 : (reg st7.data .rdx).toNat = 200 := by
    rw [show reg st7.data .rdx = _ from hm7.regs .rdx _ hrdx7]; rfl
  have hpre7 : MemcpyPre st7.data := by
    unfold MemcpyPre
    simp only [eRdi7, eRsi7, eRdx7]
    refine ⟨stackOk_callee hst hf7.kept hsp7 (by omega), Mapped.keeps houtM hf7.kept,
      mapped_off (hFm _ hf7.kept) (by decide), houtN, by unfold NativeRustcX64.NoWrap; omega,
      by unfold NativeRustcX64.Apart; omega, ?_⟩
    rw [hsp7]
    unfold NativeRustcX64.Apart
    omega
  refine call_then hpc7 hmemcpy hpre7 fun st8 hpc8 hrsp8 hpost8 ↦ ?_
  obtain ⟨-, hcp8, hs8, hsv8⟩ := hpost8
  simp only [eRdi7, eRsi7, eRdx7] at hcp8 hs8
  have hf8 : Frame m0 240 slots 8 st8.data :=
    Frame.call hf7 hsv8 hrsp8 hs8 (fun q h h' ↦ by
      rw [NativeRustcVmX64.inRange_iff, inR (by unfold NativeRustcVm.NoWrap; omega)] at h
      rw [inR hfnw, hBn] at h'
      omega) hfnw slots_le
  -- `b4`: the epilogue.
  have hwf8 := frame_wf (m0 := m0) (d := st8.data) (F := 240) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨hFm _ hf8.kept, hfnw⟩ (by simp) (List.pairwise_singleton _ _)
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf8 nofun
    (hpc8.trans (by rw [show k + NativeRustcVmX64.Vm.Seed.b3Offset + b3.length = k + NativeRustcVmX64.Vm.Seed.b4Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.Seed.b3_next]]))
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hf8.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st9 hm9 hpc9 ↦ ?_
  obtain ⟨hepi, hmem9⟩ := after_eq run_b4 ▸ ok_b4
  obtain ⟨hsv9, hrsp9⟩ := Frame.epilogue hf8 hwf8 hm9 hepi
  have hd9 : st9.data.dmem = st8.data.dmem := hm9.dmem_eq hwf8 hmem9
  simp only [PcOk] at hpc9
  refine .done _ ⟨by rw [hpc9]; exact hf8.load_ret hst (by decide), hrsp9, ?_, ?_, hsv9⟩
  · intro w hw hbc P hP
    rw [hd9]
    have h6 := hkf6 _ (hst5 w hw hbc P hP)
    have h7 : NativeRustcVm.BytesAt st7.data.dmem a
        ((keccakF1600 (Vector.ofFn (n := 25) fun i ↦ if h : i.val < 4 then
          (fiatShamirIv w.toArray)[i.val] else if h' : i.val < 8 then P[i.val - 4] else 0)).toList.flatMap
          NativeRustcVm.wordBytes) :=
      h6.of_sameOutside hs7 fun i hi h ↦ by
        rw [NativeRustcVm.length_wordsBytes, Vector.length_toList] at hi
        rw [inR (by unfold NativeRustcVm.NoWrap; omega), hBn,
          NativeRustcVm.toNat_add_ofNat (by omega)] at h
        omega
    have e := NativeRustcX64.Hasher.bytesOf_of_bytesAt h7
    rw [NativeRustcVm.length_wordsBytes, Vector.length_toList] at e
    rw [e] at hcp8
    exact hcp8
  · intro q hq
    simp only [not_or] at hq
    obtain ⟨hqo, hqs⟩ := hq
    have hqs' : ¬ ((rspOf m0).toNat - 1008 ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat) :=
      fun h ↦ hqs (hstk q h.1 h.2)
    rw [hd9, hs8 q hqo, hs7 q fun h ↦ hqs' (by
        rw [inR (by unfold NativeRustcVm.NoWrap; omega), hBn] at h
        omega),
      hs6 q fun h ↦ hqs' (by have := hR6 q h; omega),
      hs5 q fun h ↦ hqs' (by have := hs5' q h; omega), hs4 q hqs]

end

end NativeRustcVmX64.Top.Seed
