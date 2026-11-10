import Rv64Verifier.Proofs.Bus.VbbGkrCc

/-!
# `verify_bus_balance`: one iteration of the GKR loop

`gkrLoopM` with layers left, one `gkrStepM`, as the code's continuations (`gkrIter_eq`); from
`samples` to the loop's head (`smTail`); and an iteration from the loop's head (`iter`), the
callees' contracts as hypotheses.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Contracts

theorem gkrIter_eq {α : Type} {n : ℕ} (h0 : 0 < n) (st : GkrState) (tl : GkrState → TM α) :
    gkrLoopM n st >>= tl = TM.sample >>= fun comb ↦
      TM.sumcheck (polyEvalRust st.values comb) (2 ^ stepOf n + 1) (st.point.map some) >>= fun r ↦
      TM.nextScalars (2 ^ stepOf n) >>= fun c0 ↦ TM.nextScalars (2 ^ stepOf n) >>= fun c1 ↦
      TM.nextScalars (2 ^ stepOf n) >>= fun c2 ↦
      TM.require (r.2 = polyEvalRust ([c0, c1, c2].map fun child ↦
        child.foldl (fun acc value ↦ acc * value) 1) comb) >>= fun _ ↦
      TM.samples (stepOf n) >>= fun y ↦
      TM.lift ([c0, c1, c2].mapM fun child ↦ multilinearEvalRust child y) >>= fun values ↦
      gkrLoopM (n - stepOf n) ⟨values, y ++ r.1⟩ >>= tl := by
  rw [gkrLoopM_pos h0]
  simp only [gkrStepM, bind_assoc, Nat.one_shiftLeft]
  rfl

/-- From `samples`' setup at `0x80006a14` to the loop's head or exit, or out. -/
theorem smTail (hS : SamplesSpec) (hME : FunSpec Image.code 0x8000d28c
      (fun s ↦ Vbb.MleEvalPre s ∧ Rv64Verifier.Proofs.Multilinear.Bridges.MleEnds s)
      Vbb.MleEvalPost) (hCC : ConcatSpec)
    {bev : MachineState → Word → List E → Option E} {s u w₀ : MachineState} {k : Start} {cnt : E}
    {P c : Word} {n : ℕ} {st : GkrState} {x c0 c1 c2 : List E} (hpre : BusBalancePre s)
    (L : Loop bev s u k cnt P c n st) (h : AtSm s u w₀ k cnt P n x c0 c1 c2)
    (hpc : w₀.pc = 0x80006a14) (hn : 0 < n)
    (htr : Tracks (prog bev s) (s.getReg .x12) s w₀ (TM.samples (stepOf n) >>= fun y ↦
      TM.lift ([c0, c1, c2].mapM fun child ↦ multilinearEvalRust child y) >>= fun values ↦
      gkrLoopM (n - stepOf n) ⟨values, y ++ x⟩ >>= tail bev s k cnt)) :
    ∃ v, Reaches Image.code w₀ v ∧ (Done bev s v ∨ Dead Image.code v ∨
      ∃ st', Loop bev s v k cnt P (v.getMem (s.getReg .x2 - 248)) (n - stepOf n) st' ∧
        v.pc = if n - stepOf n = 0 then 0x80006c7c else 0x8000669c) := by
  have hP := L.heapP
  have hvb := L.values.buf
  rw [L.ptr] at hvb
  obtain ⟨w₁, hr₁, hd | ⟨y, hpc₁, M₁, x1₁, x10₁, x8₁, x13₁, x14₁, -, -, hc0, hc1, l0, l1, tr₁⟩⟩ :=
    samplesStep hS hpre h hpc hP.2.1 hvb.1 L.x20 L.x24 htr
  · exact ⟨w₁, hr₁, Or.inr (Or.inl hd)⟩
  have fail (o : Option (List E)) (ho : o = none)
      (hm : ([c0, c1, c2].mapM fun child ↦ multilinearEvalRust child y) = o) :
      ∀ T, TranscriptAt s (s.getReg .x12) T → (prog bev s).run T = none :=
    tr₁.fail fun T _ ↦ by rw [hm, ho]; rfl
  -- the first child
  obtain ⟨w₂, hr₂, hd | hd | ⟨v0, e0, hpc₂, M₂, he₂, rg₂, tt₂, kh₂⟩⟩ :=
    mleRun hME hpre M₁ hpc₁ (Or.inl ⟨x1₁, rfl⟩) x10₁ hc0 l0 x13₁ x14₁
      fun hm ↦ fail none rfl (by simp [List.mapM_cons, hm])
  · exact ⟨w₂, hr₁.trans hr₂, Or.inl hd⟩
  · exact ⟨w₂, hr₁.trans hr₂, Or.inr (Or.inl hd)⟩
  obtain ⟨w₃, hr₃, hpc₃, M₃, x1₃, x10₃, x27₃, hc1₃, x13₃, x14₃, tt₃⟩ :=
    push0Step hpre M₂ hpc₂ he₂ ((rg₂ .x8 (by decide)).trans x8₁) (by
      rw [rg₂ .x26 (by decide), rg₂ .x21 (by decide)]; exact kh₂ _ _ _ hc1)
  -- the second
  obtain ⟨w₄, hr₄, hd | hd | ⟨v1, e1, hpc₄, M₄, he₄, rg₄, tt₄, -⟩⟩ :=
    mleRun hME hpre M₃ hpc₃ (Or.inr (Or.inl ⟨x1₃, rfl⟩)) x10₃ hc1₃ l1 (x13₃.trans M₃.y19)
      (x14₃.trans M₃.y22) fun hm ↦ fail none rfl (by simp [List.mapM_cons, e0, hm])
  · exact ⟨w₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inl hd⟩
  · exact ⟨w₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr (Or.inl hd)⟩
  obtain ⟨w₅, hr₅, hpc₅, M₅, x1₅, x10₅, x27₅, x21₅, hc2₅, x13₅, x14₅, tt₅⟩ :=
    push1Step hpre M₄ hpc₄ he₄
  -- the third
  obtain ⟨w₆, hr₆, hd | hd | ⟨v2, e2, hpc₆, M₆, he₆, rg₆, tt₆, -⟩⟩ :=
    mleRun hME hpre M₅ hpc₅ (Or.inr (Or.inr ⟨x1₅, rfl⟩)) x10₅ hc2₅ M₅.l2 (x13₅.trans M₅.y19)
      (x14₅.trans M₅.y22) fun hm ↦ fail none rfl (by simp [List.mapM_cons, e0, e1, hm])
  · exact ⟨w₆, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₆)))), Or.inl hd⟩
  · exact ⟨w₆, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₆)))), Or.inr (Or.inl hd)⟩
  have hmap : ([c0, c1, c2].mapM fun child ↦ multilinearEvalRust child y) = some [v0, v1, v2] := by
    simp [List.mapM_cons, e0, e1, e2]
  have tr₆ := (tr₁.bind (v := w₆) (x := [v0, v1, v2]) fun T hT ↦
    ⟨T, by rw [hmap]; rfl, tt₆ T (tt₅ T (tt₄ T (tt₃ T (tt₂ T hT))))⟩)
  obtain ⟨z, hrz, hd | ⟨Lz, hpcz⟩⟩ := ccStep hCC hpre M₆ hpc₆ he₆
    (by rw [rg₆ .x27 (by decide), x27₅, rg₄ .x27 (by decide), x27₃])
    (by rw [rg₆ .x21 (by decide), x21₅]) hvb hn tr₆
  · exact ⟨z, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans (hr₆.trans hrz))))),
      Or.inr (Or.inl hd)⟩
  exact ⟨z, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans (hr₆.trans hrz))))),
    Or.inr (Or.inr ⟨_, Lz, hpcz⟩)⟩

/-- **One iteration of the GKR loop**, the callees' contracts as hypotheses. -/
theorem iter (hD : DuplexSpec) (hPE : MultilinearContracts.PolyEvalSpec)
    (hTA : TryAllocZeroedSpec) (hRF : ReserveFastSpec 0x8001086c) (hSC : SumcheckSpec)
    (hN : NextScalarsSpec) (hMul : MulSpec) (hMC : Runtime.MemcpySpec 0x800126e4)
    (hS : SamplesSpec) (hME : FunSpec Image.code 0x8000d28c
      (fun s ↦ Vbb.MleEvalPre s ∧ Rv64Verifier.Proofs.Multilinear.Bridges.MleEnds s)
      Vbb.MleEvalPost) (hCC : ConcatSpec) (bev : MachineState → Word → List E → Option E) :
    Iter bev := by
  intro s u k cnt P c n st hpre L hpc hn
  have htr := L.tracks
  rw [gkrIter_eq hn] at htr
  obtain ⟨v₁, hr₁, hd | ⟨comb, hpc₁, A₁, tr₁⟩⟩ := combStep hD hPE hpre L hpc htr
  · exact ⟨v₁, hr₁, Or.inr (Or.inl hd)⟩
  obtain ⟨v₂, hr₂, hd | ⟨hpc₂, A₂, tt₂⟩⟩ := eqsStep hTA hRF hpre A₁ hpc₁ L.x19 L.x24
  · exact ⟨v₂, hr₁.trans hr₂, Or.inr (Or.inl hd)⟩
  obtain ⟨v₃, hr₃, hd | hd | ⟨x, cl, hpc₃, A₃, tr₃⟩⟩ :=
    sumcheckStep hSC hpre A₂ hpc₂ L.inv.mono L.x9 L.x20 L.x25 (tr₁.keep tt₂)
  · exact ⟨v₃, hr₁.trans (hr₂.trans hr₃), Or.inl hd⟩
  · exact ⟨v₃, hr₁.trans (hr₂.trans hr₃), Or.inr (Or.inl hd)⟩
  obtain ⟨v₄, hr₄, hd | hd | ⟨c0, c1, c2, hpc₄, A₄, tr₄⟩⟩ :=
    nsStep hN hpre A₃ hpc₃ L.inv.mono L.x9 L.x20 L.x25 tr₃
  · exact ⟨v₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inl hd⟩
  · exact ⟨v₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr (Or.inl hd)⟩
  obtain ⟨v₅, hr₅, hd | hd | ⟨hpc₅, A₅, tr₅⟩⟩ :=
    claimCheck hMul hMC hPE hpre A₄ hpc₄ L.x20 L.x24 tr₄
  · exact ⟨v₅, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inl hd⟩
  · exact ⟨v₅, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inr (Or.inl hd)⟩
  obtain ⟨v₆, hr₆, res⟩ := smTail hS hME hCC hpre L A₅ hpc₅ hn tr₅
  exact ⟨v₆, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₆)))), res⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
