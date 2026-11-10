import Rv64Verifier.Proofs.Walk.R20B
import Rv64Verifier.Proofs.Walk.R20R

/-!
# `walk` R20, `verify_keccak`'s call

`r20call`: from `AtKC` the call returns to `0x80003f00` (`KcRet`) having written its result at
`S - 928`, the sponge, the stack and the heap it allocates; on `Ok` the code runs `afterKeccak` on
the openings the result holds (`kOpOf`) and the stream's positions before and after.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Bus Rv64Verifier.Gkr Rv64Verifier.Model.Gkr Rv64Verifier.Blocks.F4

/-- Back at `0x80003f00` from `verify_keccak`, entered at `c`. -/
structure KcRet (OI : MachineState → Word → List (List Opening) → Prop)
    (s u₀ w t c v : MachineState) (layout : LayoutMirror.LayoutRust) (rows : List (BitVec 64))
    (lir : BitVec 64) (bus : BusResultRust) (evs : List (List E × List E)) (P C L : Word)
    (cl : List ColumnClaim) : Prop where
  pc : v.pc = 0x80003f00
  rest : Rest s u₀ v
  x22 : v.getReg .x22 = lir
  x23 : v.getReg .x23 = s.getReg .x10
  x24 : v.getReg .x24 = s.getReg .x2 - 512
  x25 : v.getReg .x25 = L
  x26 : v.getReg .x26 + 1 = L
  before : heapNext t ≤ heapNext c ∧ P.toNat + 56 * C.toNat ≤ heapNext c
  ok : vecCap v (s.getReg .x2 - 928) ≠ errNiche →
    CoreT OI s u₀ w t v layout lir evs P C L.toNat cl
      (afterKeccak layout rows lir bus cl (kOpOf v (s.getReg .x2 - 928),
        (c.getMem (tp s + 344)).toNat, (v.getMem (tp s + 344)).toNat)) ∧
    NewVecE c v (s.getReg .x2 - 928) (kOpOf v (s.getReg .x2 - 928)).inputs.1 ∧
    NewVecE c v (s.getReg .x2 - 904) (kOpOf v (s.getReg .x2 - 928)).inputs.2 ∧
    OutputsAt c v (s.getReg .x2 - 880) (kOpOf v (s.getReg .x2 - 928)).outputs ∧
    4 ≤ (kOpOf v (s.getReg .x2 - 928)).inputs.1.length ∧
    (kOpOf v (s.getReg .x2 - 928)).inputs.2.length = Verifier.kBits

section Call
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t c : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {P C L : Word} {cl : List ColumnClaim}

set_option maxHeartbeats 1600000 in
/-- `verify_keccak` returns, or the run dies. -/
theorem r20call (hVK : VerifyKeccakSpecE) (hpre : WalkPre s)
    (K : AtKC OI s u₀ w t c layout rows lir bus evs P C L cl) :
    ∃ v, Reaches Image.code c v ∧
      (KcRet OI s u₀ w t c v layout rows lir bus evs P C L cl ∨ Dead Image.code v) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have H := K.core
  have I := H.rest.inv
  obtain ⟨v, hrv, ⟨hpcv, hp, post⟩ | hd⟩ := hVK.call (Reaches.refl c) K.pc K.pre
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have x10 : c.getReg .x10 = s.getReg .x2 - 928 := K.x10
  have hsl := stackLo_callee I verifyKeccakStack
  have hm : verifyKeccakStack ≤ 8736 := by decide
  have Wok : ∀ a, Within a (s.getReg .x2 - 928) 96 → InF s a ∧ ¬ KeepR s u₀ a := fun a ha ↦
    range_ok hpre H.rest (c := 928) (k := 928) (n := 96) rfl (by omega) (by omega) ha
  have st : StepW s c v (Within · (s.getReg .x2 - 928) 96) True := by
    refine ⟨post.frame.mono fun a ha ↦ ?_, post.heap, post.mono, hp .x2 (by decide)⟩
    rw [x10, K.x11, hsl] at ha
    rcases ha with ha | ha | ha | ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨trivial, by rw [tp] at ha ⊢; addr_omega [ha, hb1]⟩)))
    · exact Or.inr (Or.inl (by simp only [verifyKeccakStack] at ha; addr_omega [ha, hb1]))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  have R := H.rest.stepW hpre Wok st
  have reg (r : Reg) (hr : r ∈ calleeSaved) : v.getReg r = c.getReg r := hp r hr
  refine ⟨v, hrv, Or.inl {
    pc := by rw [hpcv, returnAddress, K.x1]; decide
    rest := R
    x22 := by rw [reg .x22 (by decide), K.x22]
    x23 := by rw [reg .x23 (by decide), K.x23]
    x24 := by rw [reg .x24 (by decide), K.x24]
    x25 := by rw [reg .x25 (by decide), K.x25]
    x26 := by rw [reg .x26 (by decide), K.x26]
    before := ⟨H.tmono, H.buf.2.1⟩
    ok := fun hok ↦ ?_ }⟩
  -- the openings, for every transcript
  have run : ∀ T, TranscriptAt c (tp s) T → ∃ T', (keccakPhaseRust layout evs).run T =
      some ((kOpOf v (s.getReg .x2 - 928), (c.getMem (tp s + 344)).toNat,
        (v.getMem (tp s + 344)).toNat), T') ∧ TranscriptAt v (tp s) T' ∧
      NewVecE c v (s.getReg .x2 - 928) (kOpOf v (s.getReg .x2 - 928)).inputs.1 ∧
      NewVecE c v (s.getReg .x2 - 904) (kOpOf v (s.getReg .x2 - 928)).inputs.2 ∧
      OutputsAt c v (s.getReg .x2 - 880) (kOpOf v (s.getReg .x2 - 928)).outputs ∧
      4 ≤ (kOpOf v (s.getReg .x2 - 928)).inputs.1.length ∧
      (kOpOf v (s.getReg .x2 - 928)).inputs.2.length = Verifier.kBits := by
    intro T hT
    have h5 := K.h5
    rw [keccakPhase_run layout evs K.h5 K.h65 T]
    have hv := post.value T (by rw [K.x11]; exact hT)
    rw [K.shape, K.inst, K.output, x10, K.x11] at hv
    have hR := returns_verifyKeccak ⟨layout.keccakLogSteps, 12⟩ evs[5].1 ((evs[5].2.drop 40).take 25) T
    generalize (verifyKeccakRust ⟨layout.keccakLogSteps, 12⟩ evs[5].1
      ((evs[5].2.drop 40).take 25)).run T = o at hv hR ⊢
    rcases o with _ | ⟨o, T'⟩
    · exact absurd hv hok
    · obtain ⟨-, n1, n2, n3, hT'⟩ := hv
      rw [show s.getReg .x2 - 928 + 24 = s.getReg .x2 - 904 by bv_omega] at n2
      rw [show s.getReg .x2 - 928 + 48 = s.getReg .x2 - 880 by bv_omega] at n3
      have e := kOpOf_eq n1 (by rwa [show s.getReg .x2 - 928 + 24 = s.getReg .x2 - 904 by bv_omega])
        (by rwa [show s.getReg .x2 - 928 + 48 = s.getReg .x2 - 880 by bv_omega])
      have hl := hR o T' rfl
      refine ⟨T', ?_, hT', by rw [e]; exact n1, by rw [e]; exact n2, by rw [e]; exact n3,
        by rw [e]; exact hl.1, by rw [e]; exact hl.2⟩
      simp only [Option.bind_some]
      rw [e, ← hT.streamOffset, ← hT'.streamOffset]
  obtain ⟨T₀, hT₀⟩ := transcriptAt_exists c (tp s)
  obtain ⟨-, -, -, n1, n2, n3, l1, l2⟩ := run T₀ hT₀
  refine ⟨H.step hpre st (fun a ha ↦ ⟨(Wok a ha).1, (Wok a ha).2, by
      rw [tp]; simp only [Within] at ha ⊢; addr_omega [ha, hb1]⟩)
    (fun a ha ↦ by simp only [Within] at ha ⊢; constructor <;> addr_omega [ha, hb1])
    (H.tracks.bind (keeps_keccakPhaseRust layout evs) fun T hT ↦ by
      obtain ⟨T', e, hT', -⟩ := run T hT
      exact ⟨T', e, hT'⟩), n1, n2, n3, l1, l2⟩

end Call

end Rv64Verifier.Proofs.Walk
