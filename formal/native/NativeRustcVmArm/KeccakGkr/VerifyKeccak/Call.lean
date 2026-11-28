module

public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Chg

/-!
# A call, its change as numbers

`callC`: a block writing the frame's ranges `Lb`, then a call whose callee changes `WS m0 L O`
(its stack within the stack below the frame): the change of the block (`Chg m0 Lb []`) and of the
call (`Chg m0 L O`). What a change keeps, its side conditions decided on the literal lists: a frame
word (`Chg.word`), frame elements (`Chg.ews`), a claim in the frame (`Chg.claim`), elements of an
output (`Chg.ewsOut`), bit weights in the scratch (`Chg.wts`), `Mid` (`Mid.chg`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt)
open NativeRustcVm.Layout (Same)

public section

variable {m0 : MachineData}

theorem kept_tr {d1 d2 d3 : DataMem} (h1 : Kept d1 d2) (h2 : Kept d2 d3) : Kept d1 d3 :=
  fun p h ↦ h2 p (h1 p h)

theorem inR_of_nat {x q : BitVec 64} {n : Nat} (hnw : x.toNat + n ≤ 2 ^ 64)
    (h : x.toNat ≤ q.toNat ∧ q.toNat < x.toNat + n) : InRange x n q :=
  (NativeRustcVm.inRange_iff hnw).mpr h

section
variable [Labels] {a : DecArea} {inst : Array EW}

/-- An output region's bytes are the outputs'. -/
theorem ob_outs (hn : Nums a inst m0) {i : Nat} (hi : i < 4) {q : BitVec 64}
    (h1 : (ob m0 i).toNat ≤ q.toNat) (h2 : q.toNat < (ob m0 i).toNat + osz i) : outs m0 q := by
  have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl
  · exact .inl (inR_of_nat hn.tW ⟨h1, h2⟩)
  · exact .inr (.inl (inR_of_nat hn.sW ⟨h1, h2⟩))
  · exact .inr (.inr (.inl (inR_of_nat hn.cW ⟨h1, h2⟩)))
  · exact .inr (.inr (.inr (inR_of_nat hn.oW ⟨h1, h2⟩)))

/-- **`WS` within a call's footprint**: the stack below the frame, the frame from `lo`, the
outputs. -/
theorem ws_call (hn : Nums a inst m0) {st : MachineData} (hfr : VFr m0 st)
    {L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)} {lo n : Nat} (hlo : lo + n ≤ 3264)
    (hL : L.all (fun p ↦ decide (lo ≤ p.1) && decide (p.2 ≤ lo + n)) = true)
    (hO : okO O = true) {q : BitVec 64} (h : WS m0 L O q) :
    InRange (stackBelow st 3648) 3648 q ∨ InRange (fb m0 + BitVec.ofNat 64 lo) n q ∨
      outs m0 q := by
  have := hn.hN
  have := m0.regs.SP.toNat_lt
  rcases h with h1 | ⟨p, hp, h1⟩ | ⟨e, he, h1⟩
  · have e := sb_toNat hn.hN hfr (n := 3648) le_rfl
    have h3 : (stackBelow st 3648).toNat + 3648 ≤ 2 ^ 64 := by rw [e]; omega
    exact .inl (inR_of_nat h3 ⟨by rw [e]; omega, by rw [e]; omega⟩)
  · simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hL
    have := hL p hp
    refine .inr (.inl (inR_of_nat ?_ ?_)) <;>
      rw [show fb m0 + BitVec.ofNat 64 lo = loc m0 lo from rfl, loc_toNat hn.hN (by omega)] <;>
      omega
  · obtain ⟨hi, hle⟩ := okO_mem hO he
    exact .inr (.inr (ob_outs hn hi (by omega) (by omega)))

/-- A frame word a change misses. -/
theorem Chg.word (hn : Nums a inst m0) {L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)}
    {d d' : Mem 64} (hc : Chg m0 L O d d') (hO : okO O = true) {o : Nat} (ho : o + 8 ≤ 3360)
    (hL : L.all (fun p ↦ decide (p.2 ≤ o) || decide (o + 8 ≤ p.1)) = true) {w : UInt64}
    (h : NativeRustcVm.WordAt d (loc m0 o) w) : NativeRustcVm.WordAt d' (loc m0 o) w :=
  NativeRustcVm.Layout.WordAt.of_same h (hc.frame hn hO ho hL) le_rfl

/-- Frame bytes a change misses. -/
theorem Chg.bytes (hn : Nums a inst m0) {L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)}
    {d d' : Mem 64} (hc : Chg m0 L O d d') (hO : okO O = true) {o k : Nat} (ho : o + k ≤ 3360)
    (hL : L.all (fun p ↦ decide (p.2 ≤ o) || decide (o + k ≤ p.1)) = true) {bs : List UInt8}
    (hl : bs.length ≤ k) (h : NativeRustcVm.BytesAt d (loc m0 o) bs) :
    NativeRustcVm.BytesAt d' (loc m0 o) bs :=
  NativeRustcVm.Layout.BytesAt.of_same h (hc.frame hn hO ho hL) hl

/-- Frame elements a change misses. -/
theorem Chg.ews (hn : Nums a inst m0) {L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)}
    {d d' : Mem 64} (hc : Chg m0 L O d d') (hO : okO O = true) {o k : Nat} (ho : o + k ≤ 3360)
    (hL : L.all (fun p ↦ decide (p.2 ≤ o) || decide (o + k ≤ p.1)) = true) {xs : List EW}
    (hl : 16 * xs.length ≤ k) (h : NativeRustcVm.EWsAt d (loc m0 o) xs) :
    NativeRustcVm.EWsAt d' (loc m0 o) xs :=
  NativeRustcVm.Tables.EWsAt.of_same h (hc.frame hn hO ho hL) hl

/-- A claim in the frame a change misses. -/
theorem Chg.claim (hn : Nums a inst m0) {L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)}
    {d d' : Mem 64} (hc : Chg m0 L O d d') (hO : okO O = true) {o : Nat} (ho : o + 768 ≤ 3360)
    (hL : L.all (fun p ↦ decide (p.2 ≤ o) || decide (o + 768 ≤ p.1)) = true)
    {c : KeccakClaimW} (h : ClaimAt d (loc m0 o) c) : ClaimAt d' (loc m0 o) c :=
  ClaimAt.img h (Img.of_same (hc.frame hn hO ho hL))

/-- Elements of an output a change misses. -/
theorem Chg.ewsOut (hn : Nums a inst m0) {L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)}
    {d d' : Mem 64} (hc : Chg m0 L O d d') (hLok : okL L = true) (hO : okO O = true)
    {i o k : Nat} (hi : i < 4) (hk0 : 0 < k) (hon : o + k ≤ osz i)
    (hOi : O.all (fun e ↦ decide (e.1 ≠ i) || decide (e.2.2 ≤ o) || decide (o + k ≤ e.2.1)) =
      true) {xs : List EW} (hl : 16 * xs.length ≤ k)
    (h : NativeRustcVm.EWsAt d (ob m0 i + BitVec.ofNat 64 o) xs) :
    NativeRustcVm.EWsAt d' (ob m0 i + BitVec.ofNat 64 o) xs :=
  NativeRustcVm.Tables.EWsAt.of_same h (hc.out hn hLok hO hi hk0 hon hOi) hl

/-- Bit weights in the scratch a change misses. -/
theorem Chg.wts (hn : Nums a inst m0) {L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)}
    {d d' : Mem 64} (hc : Chg m0 L O d d') (hLok : okL L = true) (hO : okO O = true) {o : Nat}
    (hon : o + 25600 ≤ 205824)
    (hOi : O.all (fun e ↦ decide (e.1 ≠ 1) || decide (e.2.2 ≤ o) || decide (o + 25600 ≤ e.2.1)) =
      true) {c : KeccakClaimW} (h : WeightsAt d (scA m0 + BitVec.ofNat 64 o) c) :
    WeightsAt d' (scA m0 + BitVec.ofNat 64 o) c :=
  ⟨h.1, hc.ewsOut hn hLok hO (i := 1) (by decide) (by decide) hon hOi
    (by rw [Array.length_toList, h.1]; decide) h.2⟩

end

/-- **A block writing the frame's ranges `Lb`, then a call** whose callee changes `WS m0 L O`. -/
theorem callC [Host] {a : DecArea} {inst : Array EW} (hn : Nums a inst m0)
    {ds : List Directive} {i : Nat} {rs : List (BitVec 64 × Nat)} {S0 S' : SState} {l : Label}
    {P : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    {Lb L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)} {lo n : Nat}
    {R : MachineState → Prop} {m : MachineData}
    (hk : ds.IsInfixAt Host.prog i) (hrun : exec ds S0 = some (S', .call l))
    (hfr : VFr m0 m) (hm : Match (Env.ofMachine m ((fb m0, 3360) :: rs)) S0 m)
    (hwf : (Env.ofMachine m ((fb m0, 3360) :: rs)).WF) (hsp : S'.sp = S0.sp)
    (hw : S'.mem.all (fun w ↦ w.r == 0 &&
      Lb.any (fun p ↦ decide (p.1 ≤ w.off) && decide (w.off + w.n ≤ p.2))) = true)
    (hLb : okL Lb = true) (hlo : lo + n ≤ 3264)
    (hL : L.all (fun p ↦ decide (lo ≤ p.1) && decide (p.2 ≤ lo + n)) = true)
    (hO : okO O = true)
    (hspec : Spec (Labels.label l) P Q)
    (hP : ∀ st : MachineData, Match (Env.ofMachine m ((fb m0, 3360) :: rs)) S' st →
      VFr m0 st → P st)
    (hQ : ∀ st m', Match (Env.ofMachine m ((fb m0, 3360) :: rs)) S' st → VFr m0 st →
      Q st m' → Chg m0 L O st.dmem m'.dmem ∧ Saved st m')
    (cont : ∀ st m2 : MachineData, Match (Env.ofMachine m ((fb m0, 3360) :: rs)) S' st →
      VFr m0 st → Q st m2 → VFr m0 m2 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.regs.getXReg r) →
      Chg m0 Lb [] m.dmem st.dmem → Chg m0 L O st.dmem m2.dmem → Kept m.dmem m2.dmem →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ := by
  refine callStep hn hk hrun hfr hm hwf hsp
    (writeOk_ranges (by simpa [okL] using hLb) hw) (N' := 3648) (lo := lo) (n := n)
    (by decide) hlo hspec hP (fun st m' hm1 hfr1 hq ↦ ?_)
    fun st m2 hm1 hfr1 hq hfr2 hcs ↦ ?_
  · obtain ⟨hc, hsv⟩ := hQ st m' hm1 hfr1 hq
    exact ⟨NativeRustcVm.SameOutside.mono hc fun q h ↦ ws_call hn hfr1 hlo hL hO h, hsv⟩
  · obtain ⟨hc, hsv⟩ := hQ st m2 hm1 hfr1 hq
    exact cont st m2 hm1 hfr1 hq hfr2 hcs (Chg.block hn hm1 hwf hw) hc
      (kept_tr (hm1.kept hwf) hsv.2.2)

/-- **`Mid` after a change** missing the word at 88, the registers kept. -/
theorem Mid.chg [Labels] {a : DecArea} {inst : Array EW} (hn : Nums a inst m0)
    {m m' : MachineData} {L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)} (h : Mid m0 m)
    (hfr : VFr m0 m') (hregs : ∀ r ∈ regsL, m'.regs.getXReg r = m.regs.getXReg r)
    (hc : Chg m0 L O m.dmem m'.dmem) (hO : okO O = true)
    (hL : L.all (fun p ↦ decide (p.2 ≤ 88) || decide (96 ≤ p.1)) = true) : Mid m0 m' :=
  ⟨hfr, h.regs.of_eq hregs, hc.word hn hO (by decide) hL h.pk⟩

/-- The registers `Regs` names, kept by a block and a call. -/
theorem regs_kept [Labels] {env : Env} {S0 S : SState} {m st m2 : MachineData}
    (hm0 : Match env S0 m) (hm : Match env S st)
    (h0 : regsL.all (fun r ↦ (S0.reg r).isSome && S.reg r == S0.reg r) = true)
    (hcs : ∀ r, calleeSaved r = true → m2.regs.getXReg r = st.regs.getXReg r) :
    ∀ r ∈ regsL, m2.regs.getXReg r = m.regs.getXReg r := by
  intro r hr
  rw [hcs r (by
    simp only [regsL, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)]
  exact Match.regs_keep hm0 hm regsL h0 r hr

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
