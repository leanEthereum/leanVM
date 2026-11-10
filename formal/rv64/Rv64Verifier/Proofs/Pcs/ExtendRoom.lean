import Rv64Verifier.Proofs.Pcs.ExtendGrow

/-!
# `Vec<StackClaim>::extend_desugared`: the value and the test for room

`d34_step`: `0x80009d34` copies the claim's value to `F + 32` and tests `len == cap`.
-/

namespace Rv64Verifier.Proofs.Pcs.Extend
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Transcript Rv64Verifier.Pcs
  Rv64Verifier.PcsContracts Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F37 LeanVM.Parameters
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- After the value's copy: the point and the value on the stack. -/
structure Base (s u w : MachineState) (k : Nat) : Prop where
  sp : w.getReg .x2 = s.getReg .x2 - 240
  keep : ∀ r ∈ [Reg.x8, .x9, .x19, .x20, .x21, .x22, .x23, .x24], w.getReg r = u.getReg r
  x25 : w.getReg .x25 = clAt s (k + 1)
  x18 : w.getReg .x18 = vecLen u (s.getReg .x10)
  heap : HeapOk w
  mono : heapNext u ≤ heapNext w
  fr : DFrame u w (StepW s u (w.getMem nextAddr))
  pt : NewVecE u w (s.getReg .x2 - 184) (stackPt s k)
  val : eAt w (s.getReg .x2 - 208) = eAt s (clAt s k + 32)
  len : vecLen w (s.getReg .x10) = vecLen u (s.getReg .x10)

/-- At `0x80009bf8`, room for one more claim. -/
structure Room (s u w : MachineState) (k : Nat) : Prop extends Base s u w k where
  pc : w.pc = 0x80009bf8
  room : (vecLen u (s.getReg .x10)).toNat < (vecCap w (s.getReg .x10)).toNat
  raw : RawVecOk w (s.getReg .x10) 88 8
  ptApart : Apart (vecPtr w (s.getReg .x2 - 184)) ((vecCap w (s.getReg .x2 - 184)).toNat * 24)
    (vecPtr w (s.getReg .x10)) ((vecCap w (s.getReg .x10)).toNat * 88)
  moved : (vecPtr w (s.getReg .x10) = vecPtr u (s.getReg .x10) ∧
      vecCap w (s.getReg .x10) = vecCap u (s.getReg .x10)) ∨
    (NewBuf u w (vecPtr w (s.getReg .x10)) ((vecCap w (s.getReg .x10)).toNat * 88) 8 ∧
      ∀ i < (vecLen u (s.getReg .x10)).toNat, ∀ j < 11,
        w.getMem (vecPtr w (s.getReg .x10) + BitVec.ofNat 64 (88 * i) + BitVec.ofNat 64 (8 * j)) =
          u.getMem (vecPtr u (s.getReg .x10) + BitVec.ofNat 64 (88 * i) + BitVec.ofNat 64 (8 * j)))

theorem d34_step {s u v : MachineState} {k : Nat} (hpre : ExtendPre s) (hp : Push s u k)
    (hm : Mid s u v k) :
    ∃ w, Reaches Image.code v w ∧ Base s u w k ∧
      w.getMem (s.getReg .x10) = u.getMem (s.getReg .x10) ∧
      w.getMem (s.getReg .x10 + 8) = u.getMem (s.getReg .x10 + 8) ∧
      ((w.pc = 0x80009bf8 ∧ vecLen u (s.getReg .x10) ≠ vecCap u (s.getReg .x10)) ∨
        (w.pc = 0x80009d58 ∧ vecLen u (s.getReg .x10) = vecCap u (s.getReg .x10))) := by
  have hI := hp.inv
  have hk := hp.lt
  have hf := facts hpre (by omega)
  have hCb := Region.bounds hf.claims
  have hCs := hpre.claims.stack
  have hb := sbounds hpre
  have hv := hpre.stack.valid
  rw [hK] at hv hCs
  have hA := hpre.self
  have hAb := Region.bounds hA.region
  have hAs := hA.stack
  rw [hK] at hAs
  have hAf := hA.free
  simp only [Outside] at hAf
  have hsi := hpre.selfIter
  have hu' : heapNext s ≤ heapNext u := hI.p.mono
  have hnxv : (v.getMem nextAddr).toNat ≤ heapEnd := hm.heap.hi
  have x9 : v.getReg .x9 = s.getReg .x10 := (hm.keep .x9 (by decide)).trans hI.x9
  have x21 : v.getReg .x21 = s.getReg .x2 - 208 := (hm.keep .x21 (by decide)).trans hI.x21
  have hA0 (o : Word) (ho : o.toNat + 8 ≤ 24) :
      v.getMem (s.getReg .x10 + o) = u.getMem (s.getReg .x10 + o) :=
    hm.fr.word (fun x hx hw ↦ by
      rcases hw with hw | hw | hw | hw
      · addr_omega [hx, hw, hsi, hAb, ho]
      · rw [hK] at hw; addr_omega [hx, hw, hAs, hAb, ho]
      · addr_omega [hx, hw, hAf.2, hAb, ho]
      · addr_omega [hx, hw.1, hw.2, hAf.1, hu', hnxv, hAb, ho]) (by addr_omega [hAb, ho])
  have hA00 : v.getMem (s.getReg .x10) = u.getMem (s.getReg .x10) := by
    simpa using hA0 0 (by decide)
  have hmiss := hpre.claims.miss (w := W s) (fun x hx hw ↦ by
      rcases hw with hw | hw
      · addr_omega [hx, hw, hpre.claimsOff.1, hCb]
      · addr_omega [hx, hw, hpre.claimsOff.2, hCb]) hnxv
  have hcv : eAt v (clAt s k + 32) = eAt s (clAt s k + 32) :=
    (hI.callFrame hm.fr hm.mono).eAt' (fun x hx ↦ hmiss x (by addr_omega [hx, hCb, hk]))
      (by addr_omega [hCb, hk])
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80009d34_spec hm.pc (by
    rv_eval [x9, x21, hm.x18]
    and_intros <;> first
      | valid_access hv [hb]
      | exact Region.valid hA.region (by addr_omega [hAb]) (by addr_omega [hAb]) (by addr_omega [hAb])
      | exact Region.valid hf.claims (by addr_omega [hCb, hk]) (by addr_omega [hCb, hk])
          (by addr_omega [hCb, hk])
      | addr_omega [hb, hAb, hAs, hCb, hk, hCs])
  have k₅ := b80009d34_keeps h₅
  have hf₅ := DFrame.of_memFrame (b80009d34_frame h₅ (by rw [x21]; addr_omega [hb]))
  rw [x21] at hf₅
  have hm₅ (a : Word) (h1 : a.toNat + 8 ≤ (s.getReg .x2).toNat - 208 ∨
      (s.getReg .x2).toNat - 184 ≤ a.toNat) (h2 : a.toNat + 8 ≤ 2 ^ 64) : t₅.getMem a = v.getMem a :=
    hf₅ a fun i hi hw ↦ by addr_omega [hw, hi, h1, h2, hb]
  have hn₅ : t₅.getMem nextAddr = v.getMem nextAddr := hm₅ _ (by addr_omega [hb]) (by addr_omega [hb])
  have hnx₅ : heapNext t₅ = heapNext v := by simp only [heapNext, hn₅]
  have hval : eAt t₅ (s.getReg .x2 - 208) = eAt v (clAt s k + 32) := by
    unfold eAt
    rw [← x21, b80009d34_m_x21_0 h₅, b80009d34_m_x21_8 h₅, b80009d34_m_x21_16 h₅, hm.x18,
      add_lit _ 32 8 40 rfl, add_lit _ 32 16 48 rfl]
  have ha16 : t₅.getMem (s.getReg .x10 + 16) = u.getMem (s.getReg .x10 + 16) :=
    (hm₅ _ (by addr_omega [hAs, hAb, hb]) (by addr_omega [hAb])).trans (hA0 16 (by decide))
  refine ⟨t₅, hr₅, ⟨(k₅ .x2 (by decide)).trans hm.sp, fun r hr ↦ ?_,
    (k₅ .x25 (by decide)).trans hm.x25, ?_, ⟨by rw [hnx₅]; exact hm.heap.lo, by rw [hnx₅]; exact hnxv⟩,
    by rw [hnx₅]; exact hm.mono, ?_, ?_, hval.trans hcv, ha16⟩,
    (hm₅ _ (by addr_omega [hAs, hAb, hb]) (by addr_omega [hAb])).trans hA00,
    (hm₅ _ (by addr_omega [hAs, hAb, hb]) (by addr_omega [hAb])).trans (hA0 8 (by decide)), ?_⟩
  · rw [keeps_sub k₅ (by decide) r hr]; exact hm.keep r hr
  · rw [b80009d34_x18 h₅, x9, hA0 16 (by decide)]; rfl
  · refine (hm.fr.mono fun a h ↦ (h.mono (by rw [hn₅])).step).trans hf₅ fun a h ↦ ?_
    exact Or.inr (Or.inr (Or.inl (by rw [hK]; addr_omega [h, hb])))
  · have hbuf := hm.pt.buf
    have hvn := hm.heap.hi
    refine NewVecE.frame hm.pt hf₅ (by rw [hnx₅]) (fun x hx hw ↦ by addr_omega [hx, hw, hb])
      (by addr_omega [hb]) fun x hx hw ↦ ?_
    rcases hbuf with ⟨-, h0 | ⟨h1, h2⟩⟩
    · simp only [Within] at hx; omega
    · addr_omega [hx, hw, h2, hvn, hb]
  · by_cases hfull : vecLen u (s.getReg .x10) = vecCap u (s.getReg .x10)
    · right
      refine ⟨b80009d34_pc_not_taken h₅ ?_, hfull⟩
      rw [x9, hA0 16 (by decide), hA00]; exact hfull
    · left
      refine ⟨b80009d34_pc_taken h₅ ?_, hfull⟩
      rw [x9, hA0 16 (by decide), hA00]; exact hfull

end Rv64Verifier.Proofs.Pcs.Extend
