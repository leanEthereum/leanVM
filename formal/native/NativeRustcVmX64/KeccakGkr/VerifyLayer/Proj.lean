module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.FrontRun
public import NativeVm.Equiv.KeccakRmfe

/-!
# `verify_layer` on x86-64: the projection's tools

The blocks of the projection's loops write nothing (but `b5`'s call): `PCore.pure` keeps the
state across one. The mask `1 << j` (`bitJ`), a projection's word and-ed with it is zero exactly
when the word's bit `j` is clear (`projBit`, by `decide` over the 16 words and 47 bits). The words
of `RMFE_PROJECT`, the instance weights and the product as the blocks load them (`projLoad`,
`muLoad`, `prodLoad`); the extra regions' environments (`wfR`, `wfSub`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes DecArea TStateAt off)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt)
open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- `1 << j`, as `b8` computes it from R14. -/
def bitJ (j : Nat) : BitVec 64 :=
  BinOp.apply .shl .W64 (BitVec.ofNat 64 1) (UnOp.apply .trunc .W32 (BitVec.ofNat 64 j))

/-- `S` keeps the registers `rs`. -/
def keepR (S : SState) (rs : List Reg64) : Bool := rs.all fun r ↦ S.reg r == some (.reg r)

/-- The projection's registers. -/
def pRegs : List Reg64 := [.rax, .r14, .rbx, .r15, .r12, .r13]

end

public section

/-- **A projection's word and the mask** is zero exactly when the word's bit `j` is clear. -/
theorem projBit : ∀ i < 16, ∀ j < 47,
    CmpOp.apply .eq .W64 (BinOp.apply .and .W64 (rmfeProjectW.getD i 0).toBitVec (bitJ j))
      (BitVec.ofNat 64 0) = !testBitW (rmfeProjectW.getD i 0) j := by
  rw [NativeVm.Equiv.rmfeProjectW_eq]
  decide +kernel

theorem projBit' : ∀ i < 16, ∀ j < 47,
    CmpOp.apply .eq .W64 (BinOp.apply .and .W64 (bitJ j) (rmfeProjectW.getD i 0).toBitVec)
      (BitVec.ofNat 64 0) = !testBitW (rmfeProjectW.getD i 0) j := by
  rw [NativeVm.Equiv.rmfeProjectW_eq]
  decide +kernel

theorem eq0 {x : BitVec 64} (h : CmpOp.apply .eq .W64 x (BitVec.ofNat 64 0) = true) : x = 0#64 := by
  simpa [CmpOp.apply] using h

theorem ewArg_zero : ewArg 0#64 0#64 = 0 := rfl

theorem ewArg_ew (x : EW) : ewArg x.c0.toBitVec x.c1.toBitVec = x := by
  unfold ewArg
  simp

theorem sel_false (x : EW) : sel false x = 0 := rfl

theorem sel_true (x : EW) : sel true x = x := rfl

theorem rmfeProjectW_size' : rmfeProjectW.size = 16 := by
  rw [NativeVm.Equiv.rmfeProjectW_eq]; rfl

variable {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- A region of the claim beside the frame. -/
theorem wfSub [Labels] (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop} {o : Nat}
    {d : MachineData} (hb : Body m0 W o d) {x : BitVec 64} {n : Nat}
    (h1 : (cA m0).toNat ≤ x.toNat) (h2 : x.toNat + n ≤ (cA m0).toNat + 768)
    {vars : Nat → BitVec 64} {ret : BitVec 64} : (envB m0 d [(x, n)] vars ret).WF := by
  have g := geo_of hpre
  have hc := g.hc; have := g.fbN; have := g.hN; have := g.hcs; have := g.top
  have hok := areas_ok (pre_areas hpre) (r := ⟨cA m0, 768⟩) (.inl (by simp))
  refine wf1 (pre_stack hpre) hb (fun i hi ↦ ?_) (by unfold NativeRustcVm.NoWrap; dsimp only; omega) ?_
  · dsimp only at hi ⊢
    have hx : x + BitVec.ofNat 64 i = cA m0 + BitVec.ofNat 64 (x.toNat - (cA m0).toNat + i) := by
      apply BitVec.eq_of_toNat_eq
      have := g.hc
      rw [NativeRustcVm.toNat_add_ofNat (by omega), NativeRustcVm.toNat_add_ofNat (by omega)]
      omega
    rw [hx]
    exact hb.fr.kept _ (hok.1 _ (by dsimp only; omega))
  · unfold NativeRustcVm.Apart
    dsimp only
    omega

/-- A read-only region beside the frame. -/
theorem wfR [Labels] (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop} {o : Nat}
    {d : MachineData} (hb : Body m0 W o d) {r : NativeRustcVm.Region}
    (hr : r ∈ [a.region, rcRegion, projectRegion, rhoRegion])
    {vars : Nat → BitVec 64} {ret : BitVec 64} : (envB m0 d [(r.addr, r.size)] vars ret).WF := by
  have g := geo_of hpre
  have hok := pre_rok hpre hr
  have h0 := pre_apart hpre (w := stackRegion m0 3232) (by simp) hr
  simp only [stackRegion] at h0
  refine wf1 (pre_stack hpre) hb (NativeRustcVm.Transcript.Mapped.keeps hok.1 hb.fr.kept) hok.2 ?_
  have := g.fbN; have hs := g.sbN; have := g.hN; have := g.top
  rw [hs] at h0
  unfold NativeRustcVm.Apart
  dsimp only
  omega

/-- `RMFE_PROJECT`'s word `i`, loaded. -/
theorem projLoad [Labels] (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop}
    (hWo : ∀ q, W q → outs m0 q) {o : Nat} {d : MachineData} (hb : Body m0 W o d)
    {vars : Nat → BitVec 64} {ret : BitVec 64} {i : Nat} (hi : i < 16) :
    (envB m0 d [(projectAddr, 128)] vars ret).load 1 (8 * i) 8 =
      (rmfeProjectW.getD i 0).toBitVec := by
  have hw : NativeRustcVm.WordsAt d.dmem projectAddr rmfeProjectW.toList := by
    have := hb.keep_ro hpre hWo (r := projectRegion) (by simp) (bs := _) (pre_proj hpre)
      (by rw [NativeRustcVm.length_wordsBytes, Array.length_toList, rmfeProjectW_size']; rfl)
    exact this
  have := hw.getElem (i := i) (by rw [Array.length_toList, rmfeProjectW_size']; exact hi)
  rw [Array.getElem_toList] at this
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [rmfeProjectW_size']; exact hi),
    Option.getD_some]
  exact load_of_wordAt this

/-- An element of the instance weights, its two words loaded from a region at it. -/
theorem muLoad [Labels] (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop}
    (hW : ∀ q, W q → wFront m0 q) {o : Nat} {d : MachineData} (hb : Body m0 W o d)
    {x : BitVec 64} {n : Nat} {vars : Nat → BitVec 64} {ret : BitVec 64} {i oo : Nat}
    (hi : i < c.mu.size) (hx : x + BitVec.ofNat 64 oo = cA m0 + 24#64 + BitVec.ofNat 64 (16 * i)) :
    ewArg ((envB m0 d [(x, n)] vars ret).load 1 oo 8) ((envB m0 d [(x, n)] vars ret).load 1 (oo + 8) 8) =
      c.mu.getD i 0 := by
  obtain ⟨-, -, h4⟩ := (hb.claim hpre hW).2.1
  have h4' : NativeRustcVm.EWsAt d.dmem (cA m0 + 24#64) c.mu.toList := by
    have e : NativeRustcVm.KeccakGkr.off (cA m0) NativeRustcVm.KeccakGkr.muOff + 8#64 =
        cA m0 + 24#64 := by
      unfold NativeRustcVm.KeccakGkr.off NativeRustcVm.KeccakGkr.muOff; bv_omega
    rw [← e]; exact h4
  have := h4'.getElem (i := i) (by rw [Array.length_toList]; exact hi)
  rw [NativeRustcVm.ewAt_iff, Array.getElem_toList] at this
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
  have hb1 : (envB m0 d [(x, n)] vars ret).base 1 = x := rfl
  have l0 : (envB m0 d [(x, n)] vars ret).load 1 oo 8 = c.mu[i].c0.toBitVec := by
    apply load_of_wordAt
    rw [hb1, hx]; exact this.1
  have l1 : (envB m0 d [(x, n)] vars ret).load 1 (oo + 8) 8 = c.mu[i].c1.toBitVec := by
    apply load_of_wordAt
    rw [hb1, show x + BitVec.ofNat 64 (oo + 8) = (x + BitVec.ofNat 64 oo) + BitVec.ofNat 64 8 by
      bv_omega, hx]; exact this.2
  rw [l0, l1, ewArg_ew]

/-- An element of the product, its two words loaded from the frame. -/
theorem prodLoad [Labels] {p : Array EW} {d : MachineData} {ex : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64}
    (h : NativeRustcVm.EWsAt d.dmem (off (stackBelow m0 2016) 472) p.toList) {j : Nat}
    (hj : j < p.size) :
    ewArg ((envB m0 d ex vars ret).load 0 (472 + 16 * j) 8)
      ((envB m0 d ex vars ret).load 0 (480 + 16 * j) 8) = p.getD j 0 := by
  have := h.getElem (i := j) (by rw [Array.length_toList]; exact hj)
  rw [NativeRustcVm.ewAt_iff, Array.getElem_toList] at this
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj, Option.getD_some]
  have hb0 : (envB m0 d ex vars ret).base 0 = stackBelow m0 2016 := rfl
  have l0 : (envB m0 d ex vars ret).load 0 (472 + 16 * j) 8 = p[j].c0.toBitVec := by
    apply load_of_wordAt
    rw [hb0, show stackBelow m0 2016 + BitVec.ofNat 64 (472 + 16 * j) =
      off (stackBelow m0 2016) 472 + BitVec.ofNat 64 (16 * j) by unfold off; bv_omega]
    exact this.1
  have l1 : (envB m0 d ex vars ret).load 0 (480 + 16 * j) 8 = p[j].c1.toBitVec := by
    apply load_of_wordAt
    rw [hb0, show stackBelow m0 2016 + BitVec.ofNat 64 (480 + 16 * j) =
      off (stackBelow m0 2016) 472 + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 8 by
        unfold off; bv_omega]
    exact this.2
  rw [l0, l1, ewArg_ew]

end

/-! ## Blocks that write nothing -/

public section

variable [Host] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData} {k : Nat}
  {p : Array EW} {s1 : TState} {j : Nat}

/-- **A block writing nothing** keeps the projection's state, and memory. -/
theorem PCore.pure (hpre : VerifyLayerPre a s c m0) {d : MachineData}
    (hc : PCore m0 a c p s1 j d) {ex : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} (hwf : (envB m0 d ex vars ret).WF) {ds : List Directive} {kk : Nat}
    {S S' : SState} {x : Exit} (hk : ds.IsInfixAt Host.prog kk) (hrun : exec ds S = some (S', x))
    (hret : ∀ l, x = .call l → ret = (Host.addrOf (kk + ds.length)).toBitVec)
    (hm : Match (envB m0 d ex vars ret) S d) (hmid : MidOk 2016 24 slots S' = true)
    (hmem : S'.mem = []) (hkr : keepR S' pRegs = true) {R : MachineState → Prop}
    (cont : ∀ st, Match (envB m0 d ex vars ret) S' st.data →
      PcOk (envB m0 d ex vars ret) x (Host.addrOf (kk + ds.length)) st →
      st.data.dmem = d.dmem → PCore m0 a c p s1 j st.data → Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf kk⟩ := by
  refine Body.blk (geo_of hpre) hc.body hwf hk hrun hret hm hmid
    (hex0 (by rw [hmem]; rfl)) fun st hm' hpc hb' _ ↦ ?_
  have hd : st.data.dmem = d.dmem := hm'.dmem_eq hwf hmem
  have hr : ∀ r ∈ pRegs, reg st.data r = reg d r := fun r hr ↦
    hm'.regs r (.reg r) (by simpa using List.all_eq_true.mp hkr r hr)
  refine cont st hm' hpc hd ⟨hb', hd ▸ hc.ts, hd ▸ hc.prod, hd ▸ hc.sp, ?_, ?_, ?_, ?_, ?_,
    hc.lt, hc.psize⟩
  · rw [hr .rax (by simp [pRegs])]; exact hc.rax
  · rw [hr .r14 (by simp [pRegs])]; exact hc.r14
  · rw [hr .rbx (by simp [pRegs])]; exact hc.rbx
  · rw [hr .r15 (by simp [pRegs])]; exact hc.r15
  · rw [hr .r12 (by simp [pRegs]), hr .r13 (by simp [pRegs])]; exact hc.acc

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
