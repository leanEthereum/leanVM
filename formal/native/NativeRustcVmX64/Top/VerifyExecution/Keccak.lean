module

public import NativeRustcVmX64.Top.VerifyExecution.Ring
public import NativeRustcVmX64.Code.Vm.KeccakPhase.Names
public import NativeRustcVmX64.Code.Vm.RingSwitch.Names
public import NativeRustcVmX64.Code.Vm.VerifyStackedOpening.Names

/-!
# `verify_execution`: `KECCAK`'s validity (x86-64)

`b14` stores the Keccak output's address at the frame's offset `40` and calls `keccak_phase` on
`KECCAK`'s log-height (the layout's word at byte `64`), the tables' evaluations, the scratch, the
column claims and the Keccak output; `b15` returns `0` when it failed, else ring switching
(`callKeccak`). Its regions (`AtCall.keccakAreas`): the written ones and the stack pairwise apart,
apart from the read ones.
-/

namespace NativeRustcVmX64.Top.VerifyExecution

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyExecution NativeRustcVmX64.Transcript
open NativeRustcVmX64.Top NativeRustcVm.Transcript NativeVm.Model
open NativeRustcVm.Top (workAreaBytes walkKeccak walkRing run_bind_eq)
open NativeRustcVm.Layout (LayoutWAt ClaimsWAt OodAt claimCap)
open NativeRustcVm.Tables (TableEvalsAt)
open NativeRustcVm.KeccakGkr (KeccakOutAt)
open LeanVM.Protocol.Verifier (opKeccak keccakOut)
local notation "Ap" => NativeRustcVm.Apart

public section

/-- `KECCAK`'s log-height in the layout's word at byte `64`. -/
theorem heightWord {d : DataMem} {x : BitVec 64} {L : LayoutW} (hL : LayoutWAt d x L) :
    NativeRustcVm.WordAt d (off x 64) (L.tableLogHeights.getD 5 0).toUInt64 := by
  have h6 := hL.heights_size
  have hw := NativeRustcVm.WordsAt.getElem hL.heights (i := 5) (by simp [h6, nTables])
  rw [off, NativeRustcVm.addr_add_add] at hw
  simp only [List.getElem_map, Array.getElem_toList] at hw
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [h6]; decide),
    Option.getD_some]
  exact hw

theorem rmfeProject_length : (NativeRustcVm.Data.Item.bytes .rmfeProject).length = 128 := by
  rw [NativeRustcVm.Data.Item.bytes, NativeRustcVm.length_wordsBytes,
    NativeRustcVm.Data.rmfeProject, List.length_map]
  rfl

theorem keccakRho_length : (NativeRustcVm.Data.Item.bytes .keccakRho).length = 100 := by
  have h4 : ∀ x, (NativeRustcVm.Data.u32Bytes x).length = 4 := fun x ↦ by
    simp [NativeRustcVm.Data.u32Bytes, NativeRustcVm.length_wordBytes]
  rw [NativeRustcVm.Data.Item.bytes, NativeRustcVm.length_flatMap_const h4]
  rfl

section
variable [Labels] {a : DecArea} {m0 d : MachineData}

theorem projectAddr_eq : projectAddr = rodataAddr .rmfeProject := rfl
theorem rhoAddr_eq : rhoAddr = rodataAddr .keccakRho := rfl

theorem projectAt_of {m : MachineData} {n : Nat} (h : RodataAt m n) : ProjectAt m := by
  have := h.bytesAt .rmfeProject
  have e : rmfeProjectW.toList = NativeRustcVm.Data.rmfeProject := by
    simp [rmfeProjectW, NativeRustcVm.Data.rmfeProject]
  unfold ProjectAt
  rw [e]
  exact this

theorem rhoAt_of {m : MachineData} {n : Nat} (h : RodataAt m n) : RhoAt m := h.bytesAt .keccakRho

/-- **`keccak_phase`'s areas.** -/
theorem AtCall.keccakAreas (h : AtCall m0 d) (g : Geo a m0) {s : TState}
    (hts : TStateAt d.dmem (reg m0 .rdi) a s) {N : Nat} (hN : N ≤ 17824) :
    Areas d N
      [⟨reg m0 .rdi, tstateBytes⟩, ⟨off (reg m0 .r8) 289728, NativeRustcVm.KeccakGkr.scratchBytes⟩,
        ⟨off (reg m0 .r8) 123992, NativeRustcVm.Layout.claimsBytes⟩,
        ⟨off (reg m0 .r8) 221280, NativeRustcVm.KeccakGkr.outBytes⟩]
      [a.region, ⟨off (reg m0 .r8) 112184, NativeRustcVm.Tables.tableEvalsBytes⟩, rcRegion,
        projectRegion, rhoRegion] := by
  have hc : (32 : Nat) ≤ 96 := by decide
  have hN' : N ≤ 17792 + 32 := by omega
  have hR := h.rodataAt g hc hN'
  have hT := h.tstateOk g hc hN'
  have hsb := h.sb g hc hN'
  have rok : ∀ t, NativeRustcVm.Region.Ok d.dmem ⟨rodataAddr t, t.bytes.length⟩ := fun t ↦
    ⟨(hR.bytesAt t).mapped, hR.noWrap t⟩
  have rst : ∀ t, Ap (stackBelow d N) (N + 8) (rodataAddr t) t.bytes.length := fun t ↦
    NativeRustcVm.Apart.symm (hR.apart t)
  have rap : ∀ {x : BitVec 64} {n : Nat}, RodataApart x n → ∀ t, Ap x n (rodataAddr t) t.bytes.length :=
    fun h t ↦ h t
  have wOk : ∀ {o n : Nat}, o < 495552 → o + n ≤ 495552 →
      NativeRustcVm.Region.Ok d.dmem ⟨off (reg m0 .r8) o, n⟩ := fun ho hn ↦
    h.readable g ho hn
  have wSt : ∀ {o n : Nat}, o < 495552 → o + n ≤ 495552 →
      Ap (stackBelow d N) (N + 8) (off (reg m0 .r8) o) n := fun ho hn ↦
    NativeRustcVm.Apart.symm (h.offStack g hc ho hn hN')
  have k1 := rc_len
  have k2 := rmfeProject_length
  have k3 := keccakRho_length
  show Areas d N
    [⟨reg m0 .rdi, 760⟩, ⟨off (reg m0 .r8) 289728, 205824⟩, ⟨off (reg m0 .r8) 123992, 97288⟩,
      ⟨off (reg m0 .r8) 221280, 1608⟩]
    [⟨a.words, 8 * a.len⟩, ⟨off (reg m0 .r8) 112184, 11808⟩, ⟨rcAddr, 192⟩, ⟨projectAddr, 128⟩,
      ⟨rhoAddr, 100⟩]
  rw [rcAddr_eq, projectAddr_eq, rhoAddr_eq, ← k1, ← k2, ← k3]
  refine ⟨fun r hr ↦ ?_, ?_, fun w hw r hr ↦ ?_⟩
  · simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl)
    · exact hts.footprint.1
    · exact wOk (o := 289728) (n := 205824) (by omega) (by omega)
    · exact wOk (o := 123992) (n := 97288) (by omega) (by omega)
    · exact wOk (o := 221280) (n := 1608) (by omega) (by omega)
    · exact hts.footprint.2.1
    · exact wOk (o := 112184) (n := 11808) (by omega) (by omega)
    · exact rok _
    · exact rok _
    · exact rok _
  · simp only [NativeRustcVm.disjoint_cons_iff, List.mem_cons, List.mem_nil_iff, or_false,
      forall_eq_or_imp, forall_eq, NativeRustcVm.disjoint_nil, and_true, stackRegion]
    exact ⟨⟨NativeRustcVm.Apart.symm hT.1, wSt (o := 289728) (n := 205824) (by omega) (by omega),
      wSt (o := 123992) (n := 97288) (by omega) (by omega),
      wSt (o := 221280) (n := 1608) (by omega) (by omega)⟩,
      ⟨NativeRustcVm.Apart.symm (g.apartWT (o := 289728) (n := 205824) (by omega) (by omega)),
        NativeRustcVm.Apart.symm (g.apartWT (o := 123992) (n := 97288) (by omega) (by omega)),
        NativeRustcVm.Apart.symm (g.apartWT (o := 221280) (n := 1608) (by omega) (by omega))⟩,
      ⟨g.apartW (o := 289728) (n := 205824) (o' := 123992) (n' := 97288) (by omega) (by omega)
        (by omega), g.apartW (o := 289728) (n := 205824) (o' := 221280) (n' := 1608) (by omega)
        (by omega) (by omega)⟩,
      g.apartW (o := 123992) (n := 97288) (o' := 221280) (n' := 1608) (by omega) (by omega)
        (by omega), fun _ h ↦ h.elim⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false, stackRegion] at hw hr
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact NativeRustcVm.Apart.symm hT.2.1
    · exact wSt (o := 112184) (n := 11808) (by omega) (by omega)
    · exact rst _
    · exact rst _
    · exact rst _
    · exact hts.footprint.2.2
    · exact NativeRustcVm.Apart.symm (g.apartWT (o := 112184) (n := 11808) (by omega) (by omega))
    · exact rap g.rt _
    · exact rap g.rt _
    · exact rap g.rt _
    · exact g.apartWA (o := 289728) (n := 205824) (by omega) (by omega)
    · exact g.apartW (o := 289728) (n := 205824) (o' := 112184) (n' := 11808) (by omega)
        (by omega) (by omega)
    · exact rap (g.wRod (o := 289728) (n := 205824) (by omega) (by omega)) _
    · exact rap (g.wRod (o := 289728) (n := 205824) (by omega) (by omega)) _
    · exact rap (g.wRod (o := 289728) (n := 205824) (by omega) (by omega)) _
    · exact g.apartWA (o := 123992) (n := 97288) (by omega) (by omega)
    · exact g.apartW (o := 123992) (n := 97288) (o' := 112184) (n' := 11808) (by omega)
        (by omega) (by omega)
    · exact rap (g.wRod (o := 123992) (n := 97288) (by omega) (by omega)) _
    · exact rap (g.wRod (o := 123992) (n := 97288) (by omega) (by omega)) _
    · exact rap (g.wRod (o := 123992) (n := 97288) (by omega) (by omega)) _
    · exact g.apartWA (o := 221280) (n := 1608) (by omega) (by omega)
    · exact g.apartW (o := 221280) (n := 1608) (o' := 112184) (n' := 11808) (by omega)
        (by omega) (by omega)
    · exact rap (g.wRod (o := 221280) (n := 1608) (by omega) (by omega)) _
    · exact rap (g.wRod (o := 221280) (n := 1608) (by omega) (by omega)) _
    · exact rap (g.wRod (o := 221280) (n := 1608) (by omega) (by omega)) _

end

variable [Host] {k : Nat}

/-- **`KECCAK`'s validity**, from `b14`: the function returns the walk's rest. -/
theorem callKeccak (hp : Placed code k)
    (hkp : ∀ a s cs layout evals, Spec (Labels.label NativeRustcVmX64.Vm.KeccakPhase.entryLabel)
      (KeccakPhasePre a s cs layout evals) (KeccakPhasePost a s cs layout evals))
    (hrs : ∀ a s point, Spec (Labels.label NativeRustcVmX64.Vm.RingSwitch.entryLabel) (RingSwitchPre a s)
      (RingSwitchPost a s point))
    (hvso : ∀ a s layout target coefficients point slices cs z value,
      Spec (Labels.label NativeRustcVmX64.Vm.VerifyStackedOpening.entryLabel)
        (VerifyStackedOpeningPre a s layout target coefficients point slices cs z value)
        (VerifyStackedOpeningPost a s layout target coefficients point cs z value))
    {a : DecArea} {m0 : MachineData} (g : Geo a m0) {st : MachineState} (h : At m0 st.data)
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b14Offset)) {rate : Nat} (h15 : (reg st.data .r15).toNat = rate)
    (h12 : reg st.data .r12 = off (reg m0 .r8) 112184)
    (h13 : reg st.data .r13 = off (reg m0 .r8) 123992)
    (hbp : reg st.data .rbp = off (reg m0 .r8) 3912)
    {s : TState} (hts : TStateAt st.data.dmem (reg m0 .rdi) a s) (hroots : s.roots.size ≤ 2)
    {L : LayoutW} (hL : LayoutWAt st.data.dmem (reg m0 .r8) L)
    {ev : Array (Array EW × Array EW)} (hev : TableEvalsAt st.data.dmem (off (reg m0 .r8) 112184) ev)
    (hk1 : (ev.getD opKeccak (#[], #[])).1.size = L.tableLogHeights.getD opKeccak 0)
    (hk2 : keccakOut ≤ (ev.getD opKeccak (#[], #[])).2.size) {cs : Array ColumnClaimW}
    (hcl : ClaimsWAt st.data.dmem (off (reg m0 .r8) 123992) cs) (hcs : cs.size < claimCap)
    {ood : StackClaimW} (hood : OodAt st.data.dmem (off (reg m0 .r8) 3912) ood) :
    Eventually (step1 Host.exe) (Done a m0 ((walkKeccak L rate ood cs ev).run s)) st := by
  have hR := g.R
  have h8 := g.e8
  have hF := g.F
  have hwN := g.wN
  have hN : keccakPhaseStack = 7024 := rfl
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 96) (rest := [(reg m0 .r8, 72)])
    (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b14Offset + b14.length)).toBitVec)
    ⟨Mapped.keeps g.fmapped h.frame.kept, g.fnw⟩
    (fun x hx ↦ by
      rw [List.mem_singleton] at hx; subst hx
      exact ⟨Mapped.keeps (NativeRustcVm.Mapped.mono g.mW (show 72 ≤ 495552 by decide))
        h.frame.kept, by show (reg m0 .r8).toNat + 72 ≤ 2 ^ 64; omega⟩)
    (List.pairwise_pair.mpr (by
      unfold NativeRustcVm.Apart; dsimp only; rw [hF]; have := g.wS; omega))
  have hm : Match (frameEnv m0 st.data 96 [(reg m0 .r8, 72)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b14Offset + b14.length)).toBitVec) workS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨h.frame.rsp_eval, known_ptr rfl h.rbx, trivial⟩ trivial
      trivial trivial
  refine exec_at (infix_of b14_in_code (by simp [b14]) hp) run_b14 hwf (fun _ _ ↦ rfl) hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hw1, hw40, hrdi, hrsi, hrdx, hrcx, hr8, hr9, hrbx, hk⟩ := after_eq run_b14 ▸ ok_b14
  have hC : AtCall m0 st1.data := ⟨Frame.of_block h.frame hwf hm1 hmid slots_le, fun q hq ↦ by
    have hs := sameOutside_low hwf hm1 (r := 0) rfl (by decide) hw1
    rw [hs q fun hq' ↦ hq (wr_s g (by
      rw [inR (by unfold NativeRustcVm.NoWrap; omega), hF] at hq'
      omega))]
    exact h.same q hq⟩
  have hs1 : NativeRustcVm.SameOutside st.data.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 96) 48) :=
    sameOutside_low hwf hm1 (r := 0) rfl (by decide) hw1
  have hs1' : ∀ q, NativeRustcVm.InRange (stackBelow m0 96) 48 q →
      vsb m0 + 17792 ≤ q.toNat ∧ q.toNat < vsb m0 + 17840 := fun q hq ↦ by
    rw [inR (by unfold NativeRustcVm.NoWrap; omega), hF] at hq
    omega
  have kr : ∀ r ∈ [Reg64.r12, .r13, .r14, .r15, .rbp], reg st1.data r = reg st.data r :=
    fun r hr ↦ hm1.regs r (.reg r) (by simpa using List.all_eq_true.mp hk r hr)
  have eRbx : reg st1.data .rbx = reg m0 .r8 := (hm1.regs .rbx _ hrbx).trans (eval_ptr rfl)
  have eptr : ∀ c : Nat, (Sym.ptr 1 (c : Int)).eval (frameEnv m0 st.data 96 [(reg m0 .r8, 72)]
      (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b14Offset + b14.length)).toBitVec) = off (reg m0 .r8) c := fun c ↦ by
    show (frameEnv m0 st.data 96 [(reg m0 .r8, 72)] (fun _ ↦ 0) _).base 1 + BitVec.ofInt 64 (c : Int) = _
    rw [BitVec.ofInt_natCast]; rfl
  have eRdi : reg st1.data .rdi = reg m0 .rdi := (hm1.regs .rdi _ hrdi).trans h.r14
  have eRdx : reg st1.data .rdx = off (reg m0 .r8) 112184 := (hm1.regs .rdx _ hrdx).trans h12
  have eRcx : reg st1.data .rcx = off (reg m0 .r8) 289728 := (hm1.regs .rcx _ hrcx).trans (eptr _)
  have eR8 : reg st1.data .r8 = off (reg m0 .r8) 123992 := (hm1.regs .r8 _ hr8).trans h13
  have eR9 : reg st1.data .r9 = off (reg m0 .r8) 221280 := (hm1.regs .r9 _ hr9).trans (eptr _)
  have hhl : L.tableLogHeights.getD 5 0 ≤ 30 := by
    have h6 := hL.heights_size
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [h6]; decide),
      Option.getD_some]
    exact hL.heights_le _ (Array.getElem_mem _)
  have eRsi : (reg st1.data .rsi).toNat = L.tableLogHeights.getD opKeccak 0 := by
    rw [show reg st1.data .rsi = _ from hm1.regs .rsi _ hrsi,
      show (Sym.load 1 64 8).eval _ = _ from load_ofMachine (r := 1) (b := reg m0 .r8) (n := 72)
        rfl (heightWord hL)]
    show (L.tableLogHeights.getD 5 0).toUInt64.toNat = L.tableLogHeights.getD 5 0
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  -- the memory the block keeps
  have hsW : ∀ {o n : Nat}, o < 495552 → o + n ≤ 495552 →
      NativeRustcVm.Layout.Same st.data.dmem st1.data.dmem (off (reg m0 .r8) o) n := fun ho hn ↦
    g.same hs1 ho hn fun q hq ↦ by have := hs1' q hq; have := g.wS; omega
  have hts1 : TStateAt st1.data.dmem (reg m0 .rdi) a s :=
    hts.frame (fun p hp ↦ hm1.kept hwf p hp) (fun q hq ↦ by
      have := hs1' q hq
      have := g.aS
      have := g.tS
      refine ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩
      · have := (inR g.tN).mp hi; omega
      · have := (inR g.aN).mp hi; omega) hs1
  have hev1 := NativeRustcVm.Top.TableEvalsAt.of_same hev (hsW (n := 11808) (by omega) (by omega))
  have hcl1 := NativeRustcVm.Tables.ClaimsWAt.of_same hcl (hsW (n := 97288) (by omega) (by omega))
  have hc : (32 : Nat) ≤ 96 := by decide
  have hN' : 7024 ≤ 17792 + 32 := by decide
  have hRd := hC.rodataAt g hc hN'
  have hpre : KeccakPhasePre a s cs L ev st1.data := by
    unfold KeccakPhasePre
    simp only [eRdi, eRdx, eRcx, eR8, eR9]
    rw [hN]
    refine ⟨hC.stackOk g hc hN', hRd.rcAt, projectAt_of hRd, rhoAt_of hRd, hts1, hcl1, hcs, hev1,
      eRsi, hk1.trans eRsi.symm, hk2, hC.keccakAreas g hts1 hN', ?_⟩
    apply GotAt.symbols (symbols := ["memcpy", "memset"]) (hs := by decide)
    apply hC.got g hc hN'
    intro l hl
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨g.gotT hl, g.gotW hl (by omega) (by decide),
      g.gotW hl (by omega) (by decide), g.gotW hl (by omega) (by decide),
      g.gotA hl, g.gotW hl (by omega) (by decide), g.gotRc hl, ?_, ?_⟩
    · simpa only [projectAddr_eq, rmfeProject_length] using g.gotRod hl .rmfeProject
    · simpa only [rhoAddr_eq, keccakRho_length] using g.gotRod hl .keccakRho
  refine call_then hpc1 (hkp a s cs L ev) hpre fun st2 hpc2 hrsp2 hpost ↦ ?_
  obtain ⟨hok, hres, hch, hsv⟩ := hpost
  simp only [eRdi, eRcx, eR8, eR9, hN] at hres hch
  have hR2 : ∀ q, NativeRustcVm.InAny (⟨stackBelow st1.data 7024, 7024⟩ ::
      [⟨reg m0 .rdi, tstateBytes⟩, ⟨off (reg m0 .r8) 289728, NativeRustcVm.KeccakGkr.scratchBytes⟩,
        ⟨off (reg m0 .r8) 123992, NativeRustcVm.Layout.claimsBytes⟩,
        ⟨off (reg m0 .r8) 221280, NativeRustcVm.KeccakGkr.outBytes⟩]) q →
      (vsb m0 ≤ q.toNat ∧ q.toNat < vsb m0 + 17824) ∨
      ((reg m0 .rdi).toNat ≤ q.toNat ∧ q.toNat < (reg m0 .rdi).toNat + 760) ∨
      ((reg m0 .r8).toNat + 123992 ≤ q.toNat ∧ q.toNat < (reg m0 .r8).toNat + 495552) := by
    rintro q ⟨r, hr, hq⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · have := hC.inS g hc hN' hq; left; omega
    · exact Or.inr (Or.inl (g.inT hq))
    · have := g.inW (o := 289728) (n := 205824) (by omega) (by omega) hq; omega
    · have := g.inW (o := 123992) (n := 97288) (by omega) (by omega) hq; omega
    · have := g.inW (o := 221280) (n := 1608) (by omega) (by omega) hq; omega
  have h2 : At m0 st2.data := hC.ret g eRbx ((kr .r14 (by simp)).trans h.r14)
    hsv hrsp2 hch fun q hq ↦ by
      rcases hR2 q hq with hq | hq | hq
      · exact Or.inl hq
      · exact Or.inr (Or.inl hq)
      · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  -- what the block and the call keep
  have hsA := NativeRustcVm.Transcript.SameOutside.trans hs1 hch
  have hRA : ∀ q, (NativeRustcVm.InRange (stackBelow m0 96) 48 q ∨ NativeRustcVm.InAny
      (⟨stackBelow st1.data 7024, 7024⟩ :: [⟨reg m0 .rdi, tstateBytes⟩,
        ⟨off (reg m0 .r8) 289728, NativeRustcVm.KeccakGkr.scratchBytes⟩,
        ⟨off (reg m0 .r8) 123992, NativeRustcVm.Layout.claimsBytes⟩,
        ⟨off (reg m0 .r8) 221280, NativeRustcVm.KeccakGkr.outBytes⟩]) q) →
      (vsb m0 ≤ q.toNat ∧ q.toNat < vsb m0 + 17840) ∨
      ((reg m0 .rdi).toNat ≤ q.toNat ∧ q.toNat < (reg m0 .rdi).toNat + 760) ∨
      ((reg m0 .r8).toNat + 123992 ≤ q.toNat ∧ q.toNat < (reg m0 .r8).toNat + 495552) := by
    rintro q (hq | hq)
    · have := hs1' q hq; left; omega
    · rcases hR2 q hq with h' | h' | h'
      · left; omega
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
  have hsC : ∀ {o n : Nat}, o < 495552 → o + n ≤ 123992 →
      NativeRustcVm.Layout.Same st.data.dmem st2.data.dmem (off (reg m0 .r8) o) n :=
    fun ho hn ↦ g.same hsA ho (by omega) fun q hq ↦ by
      have := g.wS
      have := g.tw
      rcases hRA q hq with h' | h' | h' <;> omega
  have h40' : NativeRustcVm.WordAt st2.data.dmem (off (stackBelow m0 96) 40)
      (UInt64.ofBitVec (off (reg m0 .r8) 221280)) := by
    have hw := wordAt_write (r := 0) (b := stackBelow m0 96) (sz := 104) hm1 rfl (by decide) hw40
    rw [show (Sym.ptr 1 221280).eval (frameEnv m0 st.data 96 [(reg m0 .r8, 72)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b14Offset + b14.length)).toBitVec) = off (reg m0 .r8) 221280 from eptr 221280] at hw
    refine keep_off hw hch fun j h1 h2 hq ↦ ?_
    rw [NativeRustcVm.length_wordBytes] at h2
    have hq' : (off (stackBelow m0 96) j).toNat = vsb m0 + 17792 + j := by
      rw [toNat_off (by omega), hF]
    have := g.wS
    have := g.tS
    rcases hR2 _ hq with h' | h' | h' <;> omega
  -- `b15`: the test
  rw [walkKeccak, run_bind_eq]
  generalize hr : (keccakPhase L ev).run s = r at hok hres
  refine branch hp g b15_in_code (by simp [b15]) (by rw [after_eq run_b15]; exact run_b15)
    (ok_test b15 (by simp)) h2 (hpc2.trans (by rw [show k + NativeRustcVmX64.Vm.VerifyExecution.b14Offset + b14.length = k + NativeRustcVmX64.Vm.VerifyExecution.b15Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyExecution.b14_next]]))
    hok (fun hb ↦ by cases r with | none => rfl | some _ => cases hb)
    fun st3 hb h3 hd3 hk3 hpc3 ↦ ?_
  obtain ⟨⟨⟨outs, kp, ks⟩, s'⟩, rfl⟩ := Option.isSome_iff_exists.mp hb
  obtain ⟨hts', hcl', hko⟩ := hres _ _ _ _ rfl
  have hroots' : s'.roots = s.roots := (NativeVm.Math.keccakPhase_roots L ev).keeps _ _ _ hr
  have k13 : reg st3.data .r13 = reg st1.data .r13 := (hk3 .r13 (by simp)).trans (hsv.1 .r13 rfl)
  have k15 : reg st3.data .r15 = reg st1.data .r15 := (hk3 .r15 (by simp)).trans (hsv.1 .r15 rfl)
  have kbp : reg st3.data .rbp = reg st1.data .rbp := (hk3 .rbp (by simp)).trans (hsv.1 .rbp rfl)
  have hL3 : LayoutWAt st3.data.dmem (off (reg m0 .r8) 0) L := by
    rw [hd3]
    exact NativeRustcVm.Tables.LayoutWAt.of_same (by rw [off_zero]; exact hL)
      (hsC (o := 0) (n := 3912) (by omega) (by omega))
  rw [off_zero] at hL3
  exact callRing hp hrs hvso g h3 (hpc3.trans (by rw [show k + NativeRustcVmX64.Vm.VerifyExecution.b15Offset + b15.length = k + NativeRustcVmX64.Vm.VerifyExecution.b16Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyExecution.b15_next]]))
    (by rw [k15, kr _ (by simp)]; exact h15) (by rw [k13, kr _ (by simp)]; exact h13)
    (by rw [kbp, kr _ (by simp)]; exact hbp) (by rw [hd3]; exact h40') (by rw [hd3]; exact hts')
    (by rw [hroots']; exact hroots) hL3 (by rw [hd3]; exact hko) (by rw [hd3]; exact hcl')
    (by rw [hd3]; exact NativeRustcVm.Top.OodAt.of_same hood (hsC (n := 504) (by omega) (by omega)))

end

end NativeRustcVmX64.Top.VerifyExecution
