module

public import NativeRustcVmX64.Top.Verify.StageA
public import NativeRustcVm.Transcript.Update
public import NativeRustcVmX64.Code.Vm.VerifyExecution.Names

/-!
# `verify`: `TState::new` and the walk (x86-64)

`b1`, run from `SA` with the frame (region 0) and the `Decoded` (region 1, RBX), writes
`TState::new`'s fields around the seed's lanes: no waiting scalar, no ground challenge, the
`Decoded`'s three words, cursor, phase and root count zero. The `TState` in the frame then
represents the model's first state `start` (`tstateAt_start`). `verify_execution` walks from it:
`stageB`, to `SB`.
-/

namespace NativeRustcVmX64.Top.Verify

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Verify NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript NativeRustcVmX64.Top NativeVm.Model
open NativeRustcVm.Top (workAreaBytes)

public section

/-- Bytes kept where a memory changed apart from them. -/
theorem agree_apart {d d' : DataMem} {b : BitVec 64} {N : Nat} {R : BitVec 64 → Prop}
    (hN : NativeRustcVm.NoWrap b N) (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → ¬ NativeRustcVm.InRange b N q) : Agree d d' b N (fun _ ↦ False) :=
  fun j hj _ ↦ hs _ fun h ↦ hR _ h (inRange_off_self hj (by unfold NativeRustcVm.NoWrap at hN; omega))

/-- The decoded area kept where a memory changed apart from it. -/
theorem DecodedAt.keep {d d' : DataMem} {a : DecArea} {stream : Array EW}
    {openings : Array (Array OpeningW)} {R : BitVec 64 → Prop} (h : DecodedAt d a stream openings)
    (hN : NativeRustcVm.NoWrap a.words (8 * a.len)) (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → ¬ NativeRustcVm.InRange a.words (8 * a.len) q) :
    DecodedAt d' a stream openings :=
  h.agree (agree_apart hN hs hR)

/-- The `Decoded` kept where a memory changed apart from it. -/
theorem DecFieldsAt.keep {d d' : DataMem} {p : BitVec 64} {a : DecArea} {R : BitVec 64 → Prop}
    (h : DecFieldsAt d p a) (hN : NativeRustcVm.NoWrap p 24)
    (hs : NativeRustcVm.SameOutside d d' R) (hR : ∀ q, R q → ¬ NativeRustcVm.InRange p 24 q) :
    DecFieldsAt d' p a := by
  have hN' := hN
  unfold NativeRustcVm.NoWrap at hN'
  have k : ∀ {o : Nat} {w : UInt64}, o + 8 ≤ 24 → NativeRustcVm.WordAt d (off p o) w →
      NativeRustcVm.WordAt d' (off p o) w := fun {o w} ho hw ↦
    keep_off hw hs fun j h1 h2 h ↦ hR _ h (inRange_off_self (by
      rw [NativeRustcVm.length_wordBytes] at h2; omega) (by omega))
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨?_, k (by decide) h1, k (by decide) h2⟩
  have := k (o := 0) (by decide) (by rw [off_zero]; exact h0)
  rwa [off_zero] at this

variable [Host] {k : Nat}

/-- **The first state**: after `b1`, the `TState` in the frame represents `start`. -/
theorem tstateAt_start {m0 d st : MachineData} {ret : BitVec 64}
    (hm : Match (frameEnv m0 d 816 [(reg m0 .rcx, 24)] (fun _ ↦ 0) ret) (after b1 initS) st)
    {a : DecArea} {stream : Array EW} {openings : Array (Array OpeningW)}
    {bcw : List UInt64} {P : Vector UInt64 4}
    (hseed : NativeRustcVm.WordsAt st.dmem (tOf m0) (seed bcw.toArray P).toList)
    (hdec : DecFieldsAt d.dmem (reg m0 .rcx) a)
    (hD : DecodedAt st.dmem a stream openings) (hf : Footprint st.dmem (tOf m0) a) :
    TStateAt st.dmem (tOf m0) a (start bcw P stream openings) := by
  obtain ⟨-, -, hz, hz2, hd0, hd1, hd2⟩ := ok_b1
  have e0 : UInt64.ofBitVec ((Sym.lit 0).eval
      (frameEnv m0 d 816 [(reg m0 .rcx, 24)] (fun _ ↦ 0) ret)) = 0 := rfl
  have z1 : ∀ i < 14, NativeRustcVm.WordAt st.dmem (off (fb m0) (208 + 8 * i)) 0 := fun i hi ↦ by
    have := wordAt_write (r := 0) (b := fb m0) (sz := 824) hm rfl (by omega) (hz i hi)
    rwa [e0] at this
  have z2 : ∀ i < 51, NativeRustcVm.WordAt st.dmem (off (fb m0) (360 + 8 * i)) 0 := fun i hi ↦ by
    have := wordAt_write (r := 0) (b := fb m0) (sz := 824) hm rfl (by omega) (hz2 i hi)
    rwa [e0] at this
  obtain ⟨h0, h1, h2⟩ := hdec
  have l0 : (Sym.load 1 0 8).eval (frameEnv m0 d 816 [(reg m0 .rcx, 24)] (fun _ ↦ 0) ret) =
      a.words := by
    show (frameEnv m0 d 816 [(reg m0 .rcx, 24)] (fun _ ↦ 0) ret).load 1 0 8 =
      (UInt64.ofBitVec a.words).toBitVec
    exact load_ofMachine (r := 1) (b := reg m0 .rcx) (n := 24) rfl (by rw [off_zero]; exact h0)
  have l1 : (Sym.load 1 8 8).eval (frameEnv m0 d 816 [(reg m0 .rcx, 24)] (fun _ ↦ 0) ret) =
      a.len.toUInt64.toBitVec := by
    show (frameEnv m0 d 816 [(reg m0 .rcx, 24)] (fun _ ↦ 0) ret).load 1 8 8 = _
    exact load_ofMachine (r := 1) (b := reg m0 .rcx) (n := 24) rfl h1
  have l2 : (Sym.load 1 16 8).eval (frameEnv m0 d 816 [(reg m0 .rcx, 24)] (fun _ ↦ 0) ret) =
      a.l.toUInt64.toBitVec := by
    show (frameEnv m0 d 816 [(reg m0 .rcx, 24)] (fun _ ↦ 0) ret).load 1 16 8 = _
    exact load_ofMachine (r := 1) (b := reg m0 .rcx) (n := 24) rfl h2
  have w0 := wordAt_write (r := 0) (b := fb m0) (sz := 824) (o := 336) hm rfl (by decide) hd0
  have w1 := wordAt_write (r := 0) (b := fb m0) (sz := 824) (o := 344) hm rfl (by decide) hd1
  have w2 := wordAt_write (r := 0) (b := fb m0) (sz := 824) (o := 352) hm rfl (by decide) hd2
  rw [l0] at w0
  rw [l1, UInt64.ofBitVec_toBitVec] at w1
  rw [l2, UInt64.ofBitVec_toBitVec] at w2
  refine ⟨hf, ⟨hseed, Nat.zero_le _, ?_, fun i h ↦ absurd h (Nat.not_lt_zero _), ?_⟩,
    ⟨?_, ?_, ?_⟩, hD, Nat.zero_le _, ?_, Nat.zero_le _, ?_, Nat.zero_le _, ?_,
    fun i h ↦ absurd h (Nat.not_lt_zero _)⟩
  · rw [off_off]; exact z1 12 (by decide)
  · rw [off_off]; exact z1 13 (by decide)
  · rw [off_off]; exact w0
  · rw [off_off, off_off]; exact w1
  · rw [off_off, off_off]; exact w2
  · rw [off_off]; exact z2 0 (by decide)
  · rw [off_off]; exact z2 1 (by decide)
  · rw [off_off]; exact z2 50 (by decide)

/-- **`TState::new` and the walk.** -/
theorem stageB (hp : Placed code k)
    (hve : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.VerifyExecution.entryLabel) (VerifyExecutionPre a s)
      (VerifyExecutionPost a s))
    {a : DecArea} {stream : Array EW} {openings : Array (Array OpeningW)} {m0 : MachineData}
    (hpre : VerifyPre a stream openings m0) {st1 : MachineState}
    (hpc1 : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Verify.b1Offset)) (hSA : SA m0 st1.data) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Verify.b2Offset) ∧
      SB a stream openings m0 st.data) st1 := by
  have g := geo_of hpre
  obtain ⟨hst, hrod, hn32, hdecF, hdecA, ⟨hbcM, -⟩, ⟨hpubM, -⟩, ⟨hdecM, -⟩, ⟨haM, -⟩,
    ⟨hwM, -⟩, -, hapR, hbcD, hgot⟩ := hpre
  obtain ⟨hf1, hs1, hrbx1, hr121, hr131, hr141, hr151, hrbp1, hseed1⟩ := hSA
  have hS := verifyStack_eq
  have hR := g.R
  have h8 := g.e8
  have hs : 18704 ≤ (rspOf m0).toNat := by omega
  have hfnw := frame_noWrap (F := 816) hst (by omega)
  have hBn := g.F
  have hoff : ∀ j, j < 824 → (off (fb m0) j).toNat = sb m0 + 17888 + j := fun j hj ↦ by
    rw [toNat_off (by omega), hBn]
  have hT : (tOf m0).toNat = sb m0 + 17896 := by rw [hoff 8 (by decide)]
  have hFm : ∀ d : MachineData, Kept m0.dmem d.dmem →
      NativeRustcVm.Mapped d.dmem (fb m0) (816 + 8) :=
    fun d hk ↦ Mapped.keeps (frame_mapped hst (by omega)) hk
  have hstk : ∀ q, sb m0 ≤ q.toNat → q.toNat < sb m0 + 18704 →
      NativeRustcVm.InRange (stackBelow m0 18704) 18704 q := by
    intro q h1 h2
    rw [inR (by unfold NativeRustcVm.NoWrap; rw [sb_eq]; omega), sb_eq]
    omega
  have hstk' : ∀ q, NativeRustcVm.InRange (stackBelow m0 18704) 18704 q →
      sb m0 ≤ q.toNat ∧ q.toNat < sb m0 + 18704 := by
    intro q h
    rw [inR (by unfold NativeRustcVm.NoWrap; rw [sb_eq]; omega), sb_eq] at h
    exact h
  have hdecN := g.decN
  have hdecS := g.dec
  have haN := g.areaN
  have haS := g.area
  have hwS := g.work
  have hwN := g.workN
  have hdA := g.decArea
  -- `b1`: `TState::new`, `call verify_execution`.
  have hwf1 := frame_wf (m0 := m0) (d := st1.data) (F := 816) (rest := [(reg m0 .rcx, 24)])
    (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.Verify.b1Offset + b1.length)).toBitVec)
    ⟨hFm _ hf1.kept, hfnw⟩
    (fun x hx ↦ by
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨Mapped.keeps hdecM hf1.kept, hdecN⟩)
    (List.pairwise_pair.mpr (by
      unfold NativeRustcVm.Apart; dsimp only; rw [hBn]; omega))
  have hm1 : Match (frameEnv m0 st1.data 816 [(reg m0 .rcx, 24)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.Verify.b1Offset + b1.length)).toBitVec) initS st1.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf1.rsp_eval, known_ptr rfl hrbx1, trivial⟩ trivial
      trivial trivial
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf1 (fun _ _ ↦ rfl) hpc1 hm1
    fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmid2, hw2, -⟩ := after_eq run_b1 ▸ ok_b1
  obtain ⟨hrdi2, hrsi2, hrdx2, hrcx2, hr82, hrbx2, -, -, -, -, -⟩ := after_eq run_b1 ▸ regs_b1
  have hf2 : Frame m0 816 slots 0 st2.data := Frame.of_block hf1 hwf1 hm2 hmid2 slots_le
  have hsp2 : rspOf st2.data = fb m0 := by rw [hf2.sp, off_zero]
  have hs2 : NativeRustcVm.SameOutside st1.data.dmem st2.data.dmem
      (fun q ↦ Touch (fb m0) 824 (fun j ↦ j < 8 ∨ 208 ≤ j ∧ j < 768) q) :=
    sameOutside_W hwf1 hm2 (r := 0) rfl fun w hw ↦ by
      obtain ⟨hr, hb⟩ := hw2 w hw
      exact ⟨hr, by omega, fun j h1 h2 ↦ by omega⟩
  have hs2' : ∀ q, Touch (fb m0) 824 (fun j ↦ j < 8 ∨ 208 ≤ j ∧ j < 768) q →
      sb m0 + 17888 ≤ q.toNat ∧ q.toNat < sb m0 + 18656 := by
    rintro q ⟨j, hj, hW, rfl⟩
    rw [hoff j hj]
    omega
  -- what the stack changes keep
  have hsame2 : NativeRustcVm.SameOutside m0.dmem st2.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 18704) 18704) := fun q hq ↦ by
    rw [hs2 q fun h ↦ hq (hstk q (by have := hs2' q h; omega) (by have := hs2' q h; omega))]
    exact hs1 q hq
  have notStk : ∀ {b : BitVec 64} {N : Nat}, NativeRustcVm.NoWrap b N →
      (b.toNat + N ≤ sb m0 ∨ sb m0 + 18712 ≤ b.toNat) →
      ∀ q, NativeRustcVm.InRange (stackBelow m0 18704) 18704 q → ¬ NativeRustcVm.InRange b N q :=
    fun {b N} hN hA q hq h ↦ by
      have := hstk' q hq
      rw [inR hN] at h
      omega
  have eRdi : reg st2.data .rdi = tOf m0 := (hm2.regs .rdi _ hrdi2).trans hrbp1
  have eRsi : reg st2.data .rsi = reg m0 .rdi := (hm2.regs .rsi _ hrsi2).trans hr131
  have eRdx : reg st2.data .rdx = reg m0 .rsi := (hm2.regs .rdx _ hrdx2).trans hr121
  have eRcx : reg st2.data .rcx = reg m0 .rdx := (hm2.regs .rcx _ hrcx2).trans hr151
  have eR8 : reg st2.data .r8 = reg m0 .r8 := (hm2.regs .r8 _ hr82).trans hr141
  have eRbx : reg st2.data .rbx = reg m0 .rcx := (hm2.regs .rbx _ hrbx2).trans (eval_ptr rfl)
  -- the first state
  have hD2 : DecodedAt st2.data.dmem a stream openings :=
    DecodedAt.keep hdecA haN hsame2 (notStk haN haS)
  have hseed2 : NativeRustcVm.WordsAt st2.data.dmem (tOf m0)
      (seed (bcOf m0).toArray (pubOf m0)).toList := by
    refine keep_off hseed1 hs2 fun j h1 h2 ↦ not_touch (by unfold NativeRustcVm.NoWrap; omega)
      ?_ ?_
    · rw [NativeRustcVm.length_wordsBytes, Vector.length_toList] at h2; omega
    · rw [NativeRustcVm.length_wordsBytes, Vector.length_toList] at h2; omega
  have hTok : NativeRustcVm.Region.Ok st2.data.dmem ⟨tOf m0, tstateBytes⟩ :=
    ⟨mapped_off (hFm _ hf2.kept) (by show 8 + 760 ≤ 816 + 8; omega), by
      show (tOf m0).toNat + 760 ≤ 2 ^ 64
      omega⟩
  have hfoot : Footprint st2.data.dmem (tOf m0) a :=
    ⟨hTok, ⟨Mapped.keeps haM hf2.kept, haN⟩, by
      show (tOf m0).toNat + 760 ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ (tOf m0).toNat
      omega⟩
  have htst : TStateAt st2.data.dmem (tOf m0) a (start (bcOf m0) (pubOf m0) stream openings) :=
    tstateAt_start (by rw [after_eq run_b1]; exact hm2) hseed2
      (DecFieldsAt.keep hdecF hdecN hs1 fun q hq h ↦ by
        have := hstk' q hq
        rw [inR hdecN] at h
        omega) hD2 hfoot
  -- `verify_execution`'s precondition
  have hsb2 : stackBelow st2.data 17888 = stackBelow m0 18704 :=
    stackBelow_callee hsp2 (by omega)
  have hbc2 : NativeRustcVm.WordsAt st2.data.dmem (reg m0 .rdi) (bcOf m0) := by
    rcases Nat.eq_zero_or_pos (reg m0 .rsi).toNat with h0 | h0
    · rw [List.length_eq_zero_iff.mp ((length_bcOf m0).trans h0)]
      exact NativeRustcVm.wordsAt_nil _ _
    · refine (wordsAt_bcOf hbcM).of_sameOutside hsame2 fun i hi h ↦ ?_
      have hA := (g.bc h0).1
      have := g.bcN
      rw [NativeRustcVm.length_wordsBytes, length_bcOf] at hi
      have := hstk' _ h
      rw [NativeRustcVm.toNat_add_ofNat (by omega)] at this
      omega
  have hpub2 : NativeRustcVm.WordsAt st2.data.dmem (reg m0 .rdx) (pubOf m0).toList := by
    refine (wordsAt_pubOf hpubM).of_sameOutside hsame2 fun i hi h ↦ ?_
    have := g.pub
    have := g.pubN
    rw [NativeRustcVm.length_wordsBytes, Vector.length_toList] at hi
    have := hstk' _ h
    rw [NativeRustcVm.toNat_add_ofNat (by omega)] at this
    omega
  have hVE : verifyExecutionStack = 17888 := rfl
  have hrod2 : RodataAt st2.data 17888 := by
    have hsame2' : NativeRustcVm.SameOutside m0.dmem st2.data.dmem
        (NativeRustcVm.InRange (stackBelow m0 verifyStack) (verifyStack + 8)) :=
      NativeRustcVm.SameOutside.mono hsame2 fun q h ↦ by
        have := hstk' q h
        rw [hS, inR (by unfold NativeRustcVm.NoWrap; rw [sb_eq]; omega), sb_eq]
        omega
    refine RodataAt.mono hrod hsame2' (noWrap_stackBelow hst) ?_ ?_ <;> rw [hsb2, hS, sb_eq]
    omega
  have htR : RodataApart (tOf m0) tstateBytes := by
    unfold RodataApart NativeRustcVm.RodataApart
    intro t
    have h1 := hrod.apart t
    unfold NativeRustcVm.Apart at h1 ⊢
    rw [hS, sb_eq] at h1
    rw [hT]
    unfold tstateBytes
    omega
  have hstR : (stackBelow st2.data 17888).toNat = sb m0 := by
    rw [hsb2, sb_eq]
  have hpre2 : VerifyExecutionPre a (start (bcOf m0) (pubOf m0) stream openings) st2.data := by
    unfold VerifyExecutionPre
    simp only [eRdi, eRsi, eRdx, eRcx, eR8]
    refine ⟨stackOk_callee hst hf2.kept hsp2 (by omega), hrod2, hn32, htst, rfl,
      ⟨Mapped.keeps hbcM hf2.kept, g.bcN⟩, ⟨Mapped.keeps hpubM hf2.kept, g.pubN⟩,
      ⟨Mapped.keeps hwM hf2.kept, hwN⟩, ?_, ?_, (fun h0 ↦ ⟨?_, (hbcD h0).2⟩), ?_⟩
    · simp only [NativeRustcVm.disjoint_cons_iff, List.forall_mem_cons, List.mem_nil_iff,
        false_implies, implies_true, NativeRustcVm.disjoint_nil, and_true, NativeRustcVm.Apart,
        stackR, DecArea.region, hVE, hstR, hT, tstateBytes]
      have := g.pub
      have := g.pubArea
      have := g.pubWork
      have := g.areaWork
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> omega
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact htR
      · exact hapR _ (by simp)
      · exact hapR _ (by simp)
      · exact hapR _ (by simp)
    · simp only [NativeRustcVm.disjoint_cons_iff, List.forall_mem_cons, List.mem_nil_iff,
        false_implies, implies_true, NativeRustcVm.disjoint_nil, and_true, NativeRustcVm.Apart,
        stackR, DecArea.region, hVE, hstR, hT, tstateBytes]
      obtain ⟨b1, b2, b3⟩ := g.bc h0
      have := g.areaWork
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> omega
    · apply NativeRustcVmX64.GotAt.callee hgot
      · apply NativeRustcVmX64.GotAt.unchanged_stack hgot hst
        change NativeRustcVm.SameOutside m0.dmem st2.data.dmem
          (NativeRustcVm.InRange (stackBelow m0 verifyStack) verifyStack)
        rw [hS]
        exact hsame2
      · rw [hS, hVE, hsb2]
      · rw [hS, hVE, hsb2]
        omega
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · rcases List.mem_append.mp hp with hp | hp
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl | rfl | rfl
            · refine ⟨(stackBelow m0 verifyStack, verifyStack + 8), by simp, ?_, ?_⟩
              · simp only [hS, sb_eq, hT]
                omega
              · simp only [hS, sb_eq, hT, tstateBytes]
                omega
            · exact ⟨(a.words, 8 * a.len), by simp, Nat.le_refl _, Nat.le_refl _⟩
            · exact ⟨(reg m0 .rdx, 32), by simp, Nat.le_refl _, Nat.le_refl _⟩
            · exact ⟨(reg m0 .r8, workAreaBytes), by simp, Nat.le_refl _, Nat.le_refl _⟩
          · exact ⟨p, by simp [hp], Nat.le_refl _, Nat.le_refl _⟩
        · exact ⟨p, by simp [hp], Nat.le_refl _, Nat.le_refl _⟩
  refine call_then hpc2 (hve a _) hpre2 fun st3 hpc3 hrsp3 hpost3 ↦ ?_
  obtain ⟨hres3, hs3, hsv3⟩ := hpost3
  simp only [eRdi, eRsi, eRdx, eRcx, eR8] at hres3 hs3
  have hR3 : ∀ q, NativeRustcVm.InAny [⟨tOf m0, tstateBytes⟩, ⟨reg m0 .r8, workAreaBytes⟩,
      frameR st2.data verifyExecutionStack] q →
      (sb m0 ≤ q.toNat ∧ q.toNat < sb m0 + 18656) ∨ NativeRustcVm.InRange (reg m0 .r8) workAreaBytes q := by
    intro q h
    rcases inAny3 h with h | h | h
    · left
      change NativeRustcVm.InRange (tOf m0) 760 q at h
      rw [inR (by unfold NativeRustcVm.NoWrap; omega), hT] at h
      omega
    · exact Or.inr h
    · left
      change NativeRustcVm.InRange (stackBelow st2.data verifyExecutionStack) verifyExecutionStack q
        at h
      rw [hVE, inR (by unfold NativeRustcVm.NoWrap; rw [hstR]; omega), hstR] at h
      omega
  have hf3 : Frame m0 816 slots 8 st3.data := by
    refine Frame.call_low hf2 hsv3 hrsp3 hs3 (L := 768) (fun q h ↦ ?_)
      (fun p hp ↦ slots_ge p hp) (by decide) hfnw slots_le
    rw [show (stackBelow m0 816).toNat = sb m0 + 17888 from hBn]
    rcases hR3 q h with h | h
    · left; omega
    · rw [inR (by unfold NativeRustcVm.NoWrap; omega)] at h
      omega
  refine .done _ ⟨hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Verify.b1_next), ⟨hf3, fun q hq ↦ ?_,
    (hsv3.1 .rbx rfl).trans eRbx, (hres3 _ (length_bcOf m0) hbc2 _ hpub2).1,
    (hres3 _ (length_bcOf m0) hbc2 _ hpub2).2⟩⟩
  simp only [not_or] at hq
  rw [hs3 q fun h ↦ by
      rcases hR3 q h with h | h
      · exact hq.1 (hstk q h.1 (by omega))
      · exact hq.2 h]
  exact hsame2 q hq.1

end

end NativeRustcVmX64.Top.Verify
