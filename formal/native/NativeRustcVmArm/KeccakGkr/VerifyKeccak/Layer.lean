module

public import NativeRustcVmArm.Code.Vm.VerifyKeccak.Names
public import NativeRustcVmArm.Code.Vm.VerifyLayer.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Copies

/-!
# `verify_keccak`: one layer

`stepLayer`: the block calling `verify_layer(t, logSteps, j, frame + 960, scratch)` and its branch
to the failure exit: from `AtL j` to `AtL (j + 1)`, or the model's `none`. The read-only data's
regions (`ok_rc`, `ok_pj`, `ok_rh`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt)
open LeanVM.Protocol.Verifier (keccakDepth)

public section

section
variable [Labels] {a : DecArea} {s : TState} {cs : Array ColumnClaimW} {inst output : Array EW}
  {m0 : MachineData}

theorem ok_rc (h : P0 a s cs inst output m0) : Mapped m0.dmem rcAddr 192 :=
  (Areas.ok h.areas (r := rcRegion) (Or.inr (by simp [rsOf]))).1
theorem ok_pj (h : P0 a s cs inst output m0) : Mapped m0.dmem projectAddr 128 :=
  (Areas.ok h.areas (r := projectRegion) (Or.inr (by simp [rsOf]))).1
theorem ok_rh (h : P0 a s cs inst output m0) : Mapped m0.dmem rhoAddr 100 :=
  (Areas.ok h.areas (r := rhoRegion) (Or.inr (by simp [rsOf]))).1

end

variable [Host] {k : Nat} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output : Array EW} {m0 : MachineData}

/-- **Layer `j`**: `verify_layer` and its branch. -/
theorem stepLayer (hp : Placed code k) (h : P0 a s cs inst output m0) (hn : Nums a inst m0)
    (hvl : ∀ a s c, Spec (Labels.label NativeRustcVmArm.Vm.VerifyLayer.entryLabel) (VerifyLayerPre a s c)
      (VerifyLayerPost a s c))
    {ds bs : List Directive} {i i2 i3 j : Nat} {S1 S2 : SState} {cb : SBool}
    (hj : j < keccakDepth)
    (hk : ds.IsInfixAt Host.prog i) (hrun : exec ds midS = some (S1, .call NativeRustcVmArm.Vm.VerifyLayer.entryLabel))
    (hi2 : i + ds.length = i2) (hk2 : bs.IsInfixAt Host.prog i2)
    (hrun2 : exec bs midS = some (S2, .cond cb NativeRustcVmArm.Vm.VerifyKeccak.label_31)) (hi3 : i2 + bs.length = i3)
    (hS1 : S1.mem = [] ∧ S1.sp = .ptr 0 0 ∧ S1.reg .X0 = some (.reg .X20) ∧
      S1.reg .X1 = some (.reg .X21) ∧ S1.reg .X2 = some (.lit j) ∧
      S1.reg .X3 = some (.ptr 0 960) ∧ S1.reg .X4 = some (.reg .X22) ∧
      S1.reg .X19 = some (.reg .X19) ∧
      regsL.all (fun r ↦ (midS.reg r).isSome && S1.reg r == midS.reg r) = true)
    (hS2 : S2.mem = [] ∧ S2.sp = .ptr 0 0 ∧
      regsL.all (fun r ↦ (midS.reg r).isSome && S2.reg r == midS.reg r) = true ∧
      csL.all (fun r ↦ (midS.reg r).isSome && S2.reg r == midS.reg r) = true)
    (hcb : ∀ env : Env, ∀ b : Bool, env.regs .X0 = (okWord b).toBitVec → cb.eval env = !b)
    {m : MachineData} {sj : TState} {cj first : KeccakClaimW} {c : EW}
    (hl : AtL a s cs inst output m0 m j sj cj first c)
    (cont : ∀ m' sj' cj', AtL a s cs inst output m0 m' (j + 1) sj' cj' first c →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m', Host.addrOf i3⟩) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m, Host.addrOf i⟩ := by
  have hwf := envM_wf hn hl.sl.mid.fr
  subst hi2 hi3
  have hN := hn.hN
  have hSP := m0.regs.SP.toNat_lt
  have hj12 : j < 12 := hj
  have hvls : verifyLayerStack = 3648 := rfl
  obtain ⟨hmem, hsp, hx0, hx1, hx2, hx3, hx4, hx19, hrk⟩ := hS1
  refine callC hn hk hrun hl.sl.mid.fr (matchM hn hl.sl.mid.fr) hwf (by rw [hsp]; rfl)
    (by rw [hmem]; rfl) (Lb := []) (L := [(960, 1728)]) (O := [(0, 0, 760), (1, 25600, 140288)])
    (lo := 960) (n := 768) (by decide) (by decide) (by decide) (by decide) (hvl a sj cj)
    (fun st hm1 hfr1 ↦ ?_) (fun st m' hm1 hfr1 hq ↦ ?_)
    fun st m2 hm1 hfr1 hq hfr2 hcs hb hc hkt ↦ ?_
  all_goals
    have hd : st.dmem = m.dmem := hm1.dmem_eq hwf hmem
    have e0 : st.regs.X0 = m0.regs.X0 :=
      (reg_of hm1 (r := .X0) (v := .reg .X20) hx0 rfl).trans hl.sl.mid.regs.x20
    have e1 : st.regs.X1 = m0.regs.X1 :=
      (reg_of hm1 (r := .X1) (v := .reg .X21) hx1 rfl).trans hl.sl.mid.regs.x21
    have ex2 : st.regs.X2.toNat = j := by
      rw [← UInt64.toNat_toBitVec, show st.regs.X2 = st.regs.getXReg .X2 from rfl,
        hm1.regs .X2 _ hx2]
      simp only [Sym.eval, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have e3 : st.regs.X3.toBitVec = loc m0 960 := reg_loc hm1 (r := .X3) (o := 960) hx3
    have e4 : st.regs.X4 = m0.regs.X5 :=
      (reg_of hm1 (r := .X4) (v := .reg .X22) hx4 rfl).trans hl.sl.mid.regs.x22
  · refine ⟨stackOk_of hn hfr1 (by decide), rcAt_of h hn hfr1 (by decide),
      projectAt_of h hn hfr1, rhoAt_of h hn hfr1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e0, hd]; exact hl.ts
    · rw [e3, hd]; exact hl.claim
    · rw [e4, hd]; exact hl.wts
    · rw [ex2]; exact hj
    · have := h.n1; have := h.n30
      rw [e1]; constructor <;> rw [hl.psz, hl.hfirst] <;> omega
    · rw [e0, e3, e4]
      show Areas st verifyLayerStack [⟨tA m0, _⟩, ⟨loc m0 960, _⟩, ⟨scA m0, _⟩]
        [a.region, rcRegion, projectRegion, rhoRegion]
      areas_split
      all_goals first
        | exact (ok_loc hn hfr1 (by decide)).1
        | exact (ok_loc hn hfr1 (by decide)).2
        | exact (ok_of (ok_t h) hn.tW hfr1 (by decide)).1
        | exact (ok_of (ok_t h) hn.tW hfr1 (by decide)).2
        | exact (ok_of (ok_sc h) hn.sW hfr1 (by decide)).1
        | exact (ok_of (ok_sc h) hn.sW hfr1 (by decide)).2
        | exact (ok_of (ok_w h) hn.wW hfr1 le_rfl).1
        | exact (ok_of (ok_w h) hn.wW hfr1 le_rfl).2
        | exact (ok_of (ok_rc h) hn.rcW hfr1 le_rfl).1
        | exact (ok_of (ok_rc h) hn.rcW hfr1 le_rfl).2
        | exact (ok_of (ok_pj h) hn.pjW hfr1 le_rfl).1
        | exact (ok_of (ok_pj h) hn.pjW hfr1 le_rfl).2
        | exact (ok_of (ok_rh h) hn.rhW hfr1 le_rfl).1
        | exact (ok_of (ok_rh h) hn.rhW hfr1 le_rfl).2
        | apart_auto hn hfr1
  · obtain ⟨-, -, hs, hsv⟩ := hq
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q ⟨r, hr, hq⟩ ↦ ?_, hsv⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ws_stk hn hfr1 (by decide) hq
    · rw [e0] at hq
      exact ws_ob0 hn (i := 0) (n := 760) (by decide) (by decide) (by decide) (by decide) hq
    · rw [e3] at hq
      exact ws_loc hn (o := 960) (n := 768) (by decide) (by decide) hq
    · rw [e4] at hq
      exact ws_ob hn (i := 1) (o := 25600) (n := 114688) (by decide) (by decide) (by decide)
        (by decide) hq
  · obtain ⟨hx, hok, -, -⟩ := hq
    rw [e1, ex2] at hx
    rw [e1, ex2, e3, e0, e4] at hok
    have hregs : ∀ r ∈ regsL, m2.regs.getXReg r = m.regs.getXReg r :=
      regs_kept (matchM hn hl.sl.mid.fr) hm1 hrk hcs
    have h19 : m2.regs.getXReg .X19 = m.regs.getXReg .X19 :=
      keep_cs (matchM hn hl.sl.mid.fr) hm1 hcs (r := .X19) rfl rfl hx19
    have hmid2 : Mid m0 m2 :=
      Mid.chg hn hl.sl.mid hfr2 hregs (hb.trans hc) (by decide) (by decide)
    obtain ⟨hmem2, hsp2, hrk2, hck2⟩ := hS2
    refine failBranch hp hn hk2 hrun2 hmid2 hmem2 hsp2 hrk2 hck2
      (b := ((verifyKeccakLayer m0.regs.X1.toNat j cj).run sj).isSome)
      (hcb _ _ (by rw [Env.ofMachine_regs]; exact congrArg UInt64.toBitVec hx)) (fun hf ↦ ?_)
      fun hsome m' hmid' hd' hcs' ↦ ?_
    · cases hr : (verifyKeccakLayer m0.regs.X1.toNat j cj).run sj with
      | none => rw [hl.run, layersFrom_succ _ hj, bind_assoc, run_bind_none hr]
      | some _ => rw [hr] at hf; cases hf
    · obtain ⟨⟨c', s'⟩, hr⟩ : ∃ q, (verifyKeccakLayer m0.regs.X1.toNat j cj).run sj = some q := by
        cases hq : (verifyKeccakLayer m0.regs.X1.toNat j cj).run sj with
        | none => rw [hq] at hsome; cases hsome
        | some q => exact ⟨q, rfl⟩
      obtain ⟨hts', hcl', hwt'⟩ := hok c' s' hr
      rw [← hd'] at hts' hcl' hwt'
      have hc' : Chg m0 ([] ++ [(960, 1728)]) ([] ++ [(0, 0, 760), (1, 25600, 140288)])
          m.dmem m'.dmem := by rw [hd']; exact hb.trans hc
      refine cont m' s' c' ⟨SL.chg hn hl.sl hmid'.fr (fun r hr ↦ (hcs' r ?_).trans (hregs r hr))
        ((hcs' .X19 rfl).trans h19) hc' (by decide) (by decide) (by decide) (by decide),
        hts', hcl', hwt', (layer_point_size hr).trans hl.psz, hl.hfirst, ?_⟩
      · simp only [regsL, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      · rw [hl.run, layersFrom_succ _ hj, bind_assoc, run_bind_some hr]

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
