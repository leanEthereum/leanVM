module

public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Call

/-!
# `verify_keccak`: the copies' step and the layers' state

`cpC`: a block writing the frame's ranges `L`, then `memcpy` within the frame: an image of the
source at the destination (`Img`) and the change as numbers (`Chg`). `SL`: what the code keeps from
the copies to the first opening (the first claim's point at 480, its bit weights at the scratch,
the frame's words); `AtL j`: before layer `j` (`b16 + 2j`), the running claim at 960,
    its bit weights
at the scratch's `weights`, the model's run the layers from `j` on.
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt)
open NativeRustcVm.Layout (Same)

@[expose] public section

/-- **What the code keeps from the copies to the first opening.** -/
structure SL [Labels] (cs : Array ColumnClaimW) (m0 m : MachineData) (first : KeccakClaimW)
    (c : EW) : Prop where
  mid : Mid m0 m
  x19 : (m.regs.getXReg .X19).toBitVec = loc m0 1248
  cls : NativeRustcVm.Layout.ClaimsWAt m.dmem (clA m0) cs
  fsz : first.point.size ≤ 30
  fpt : NativeRustcVm.EWsAt m.dmem (loc m0 480) first.point.toList
  fw : WeightsAt m.dmem (scA m0 + BitVec.ofNat 64 0) first
  w48 : NativeRustcVm.WordAt m.dmem (loc m0 48) (UInt64.ofBitVec (loc m0 480))
  w56 : NativeRustcVm.WordAt m.dmem (loc m0 56) c.c1
  w64 : NativeRustcVm.WordAt m.dmem (loc m0 64) first.point.size.toUInt64
  w72 : NativeRustcVm.WordAt m.dmem (loc m0 72) m0.regs.X7
  w80 : NativeRustcVm.WordAt m.dmem (loc m0 80) c.c0

/-- **Before layer `j`.** -/
structure AtL [Labels] (a : DecArea) (s : TState) (cs : Array ColumnClaimW)
    (inst output : Array EW) (m0 m : MachineData) (j : Nat) (sj : TState)
    (cj first : KeccakClaimW) (c : EW) : Prop where
  sl : SL cs m0 m first c
  ts : TStateAt m.dmem (tA m0) a sj
  claim : ClaimAt m.dmem (loc m0 960) cj
  wts : WeightsAt m.dmem (scA m0 + BitVec.ofNat 64 25600) cj
  psz : cj.point.size = first.point.size
  hfirst : first.point.size = inst.size - 4 + 1
  run : run0 s inst output m0 =
    (layersFrom m0.regs.X1.toNat j cj >>= restOpen m0.regs.X1.toNat inst first c).run sj

/-- The frame ranges `SL` reads are apart from `L`. -/
def slL (L : List (Nat × Nat)) : Bool :=
  L.all fun p ↦ (decide (p.2 ≤ 48) || decide (96 ≤ p.1)) &&
    (decide (p.2 ≤ 480) || decide (960 ≤ p.1))

/-- The outputs' ranges `SL` reads (the column claims, the first bit weights) are apart from
`O`. -/
def slO (O : List (Nat × Nat × Nat)) : Bool :=
  O.all fun e ↦ decide (e.1 ≠ 2) && (decide (e.1 ≠ 1) || decide (25600 ≤ e.2.1))

end

public section

variable {m0 : MachineData}

theorem all_imp {α : Type} {L : List α} {f g : α → Bool} (h : L.all f = true)
    (hfg : ∀ x, f x = true → g x = true) : L.all g = true := by
  simp only [List.all_eq_true] at h ⊢
  exact fun x hx ↦ hfg x (h x hx)

/-- **`SL` after a change** apart from what it reads. -/
theorem SL.chg [Labels] {a : DecArea} {inst : Array EW} (hn : Nums a inst m0)
    {cs : Array ColumnClaimW} {m m' : MachineData} {first : KeccakClaimW} {c : EW}
    {L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)} (h : SL cs m0 m first c)
    (hfr : VFr m0 m') (hregs : ∀ r ∈ regsL, m'.regs.getXReg r = m.regs.getXReg r)
    (h19 : m'.regs.getXReg .X19 = m.regs.getXReg .X19)
    (hc : Chg m0 L O m.dmem m'.dmem) (hLok : okL L = true) (hO : okO O = true)
    (hL : slL L = true) (hO1 : slO O = true) : SL cs m0 m' first c := by
  have hw : ∀ o, 48 ≤ o → o + 8 ≤ 96 →
      L.all (fun p ↦ decide (p.2 ≤ o) || decide (o + 8 ≤ p.1)) = true := fun o h1 h2 ↦
    all_imp hL fun p hp ↦ by
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hp ⊢; omega
  refine ⟨Mid.chg hn h.mid hfr hregs hc hO (hw 88 (by omega) (by omega)), by rw [h19]; exact h.x19,
    hc.cls hn hLok hO (all_imp hO1 fun e he ↦ by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at he ⊢; exact he.1) h.cls, h.fsz,
    hc.ews hn hO (o := 480) (k := 480) (by omega) (all_imp hL fun p hp ↦ by
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hp ⊢; omega)
      (by rw [Array.length_toList]; have := h.fsz; omega) h.fpt,
    hc.wts hn hLok hO (o := 0) (by omega) (all_imp hO1 fun e he ↦ by
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at he ⊢; omega) h.fw,
    hc.word hn hO (by omega) (hw 48 (by omega) (by omega)) h.w48,
    hc.word hn hO (by omega) (hw 56 (by omega) (by omega)) h.w56,
    hc.word hn hO (by omega) (hw 64 (by omega) (by omega)) h.w64,
    hc.word hn hO (by omega) (hw 72 (by omega) (by omega)) h.w72,
    hc.word hn hO (by omega) (hw 80 (by omega) (by omega)) h.w80⟩

variable [Host] {a : DecArea} {inst : Array EW}

/-- **A block writing the frame's ranges `L`, then `memcpy` within the frame.** -/
theorem cpC (hn : Nums a inst m0)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    {ds : List Directive} {i : Nat} {S' : SState} {m : MachineData} {L : List (Nat × Nat)}
    {dst src n : Nat} {R : MachineState → Prop}
    (hk : ds.IsInfixAt Host.prog i) (hrun : exec ds midS = some (S', .call NativeRustcVmArm.Vm.Memcpy.entryLabel))
    (hmid : Mid m0 m) (hsp : S'.sp = .ptr 0 0)
    (hw : S'.mem.all (fun w ↦ w.r == 0 &&
      L.any (fun p ↦ decide (p.1 ≤ w.off) && decide (w.off + w.n ≤ p.2))) = true)
    (hLok : okL L = true)
    (hLs : L.all (fun p ↦ decide (p.2 ≤ src) || decide (src + n ≤ p.1)) = true)
    (hL88 : L.all (fun p ↦ decide (p.2 ≤ 88) || decide (96 ≤ p.1)) = true)
    (hrk : regsL.all (fun r ↦ (midS.reg r).isSome && S'.reg r == midS.reg r) = true)
    (hx0 : ∀ st, Match (envM m0 m) S' st → st.regs.X0.toBitVec = loc m0 dst)
    (hx1 : ∀ st, Match (envM m0 m) S' st → st.regs.X1.toBitVec = loc m0 src)
    (hx2 : S'.reg .X2 = some (.lit n))
    (hdst : dst + n ≤ 3264) (hsrc : src + n ≤ 3264) (h88 : dst + n ≤ 88 ∨ 96 ≤ dst)
    (hap : dst + n ≤ src ∨ src + n ≤ dst)
    (cont : ∀ st m2 : MachineData, Match (envM m0 m) S' st → Mid m0 m2 →
      Img m.dmem (loc m0 src) m2.dmem (loc m0 dst) n →
      Chg m0 L [] m.dmem st.dmem → Chg m0 [(dst, dst + n)] [] st.dmem m2.dmem →
      Kept m.dmem m2.dmem →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.regs.getXReg r) →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ := by
  have hwf := envM_wf hn hmid.fr
  have hN := hn.hN
  have hSP := m0.regs.SP.toNat_lt
  refine callC hn hk hrun hmid.fr (matchM hn hmid.fr) hwf hsp hw hLok (L := [(dst, dst + n)])
    (O := []) (lo := dst) (n := n) hdst (by simp) rfl hmemcpy
    (fun st hm1 hfr1 ↦ ?_) (fun st m' hm1 hfr1 hq ↦ ?_)
    fun st m2 hm1 hfr1 hq hfr2 hcs hb hc hkt ↦ ?_
  all_goals
    have e0 := hx0 st hm1
    have e1 := hx1 st hm1
    have e2 : st.regs.X2.toNat = n := by
      rw [← UInt64.toNat_toBitVec, show st.regs.X2 = st.regs.getXReg .X2 from rfl,
        hm1.regs .X2 _ hx2]
      simp only [Sym.eval, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [e2] <;> (try rw [e0]) <;> (try rw [e1])
    · exact frame_mapped' hn hfr1 (by omega)
    · exact frame_mapped' hn hfr1 (by omega)
    · exact loc_noWrap hn (by omega)
    · exact loc_noWrap hn (by omega)
    · unfold Apart; rw [loc_toNat hn.hN (by omega), loc_toNat hn.hN (by omega)]; omega
  · obtain ⟨-, -, hs, hsv⟩ := hq
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q hq ↦ ?_, hsv⟩
    rw [e0, e2] at hq
    exact ws_loc hn (List.mem_singleton_self _) (by omega) hq
  · obtain ⟨-, hcp, -, -⟩ := hq
    rw [e0, e1, e2] at hcp
    have hsame : Same m.dmem st.dmem (loc m0 src) n := hb.frame hn rfl (by omega) hLs
    have h88' : (L ++ [(dst, dst + n)]).all
        (fun p ↦ decide (p.2 ≤ 88) || decide (96 ≤ p.1)) = true := by
      rw [List.all_append, hL88]
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.true_and, Bool.or_eq_true,
        decide_eq_true_eq]
      omega
    exact cont st m2 hm1
      (Mid.chg hn hmid hfr2 (regs_kept (matchM hn hmid.fr) hm1 hrk hcs) (hb.trans hc) rfl h88')
      ((Img.of_same hsame).trans (Img.of_bytesOf hcp)) hb hc hkt hcs

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
