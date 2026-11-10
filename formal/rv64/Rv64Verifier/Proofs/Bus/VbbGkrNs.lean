import Rv64Verifier.Proofs.Bus.VbbGkrSumcheck

/-!
# `verify_bus_balance`: an iteration's three `next_scalars`

The children read into `S - 608` in turn, each kept in registers (the third's pointer at
`S - 1112`); `x`'s capacity and length saved at `S - 1120` and `S - 1144`, the layer count at
`S - 1128`; an `Err` to `0x80007100` (`err7100`). To the `checked` test at `0x80006844` (`AtCk`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem pow_step_toNat (n : Nat) : (BitVec.ofNat 64 (2 ^ stepOf n)).toNat = 2 ^ stepOf n := by
  have : 2 ^ stepOf n ≤ 4 := by unfold stepOf; split <;> decide
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem StepR.join {s u v w : MachineState} {A : Word → Prop} (h₁ : StepR s u v A)
    (h₂ : StepR s v w A) : StepR s u w A :=
  (h₁.trans h₂).weaken fun _ ha ↦ ha.elim id id

/-- A step writing only the frame keeps what the code runs. -/
theorem Tracks.keepF {α : Type} {M C : TM α} {s v w : MachineState} {X : Word → Prop}
    (hpre : BusBalancePre s) (h : Tracks M (s.getReg .x12) s v C) (I : Inv s v) (hw : HeapOk w)
    (fr : DFrame v w X) (hX : ∀ a, X a → Within a (s.getReg .x2 - 1344) 1240) :
    Tracks M (s.getReg .x12) s w C := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  exact h.keep fun T hT ↦ I.transcript hpre hw (fr.mono fun a ha ↦ Or.inl (by
    have := hX a ha; addr_omega [this, hb1])) hT

/-- A call of `next_scalars(m)` into `S - 608`. -/
theorem nsCall (hN : NextScalarsSpec) {bev : MachineState → Word → List E → Option E}
    {s v : MachineState} {k : Start} {cnt : E} {P : Word} {m : Nat} {K : List E → TM BusResultRust}
    (hpre : BusBalancePre s) (C : Ctx s v k cnt P) (hpc : v.pc = 0x80004818)
    (h10 : v.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608) (h11 : v.getReg .x11 = s.getReg .x12)
    (h12 : (v.getReg .x12).toNat = m)
    (htr : Tracks (prog bev s) (s.getReg .x12) s v (TM.nextScalars m >>= K)) :
    ∃ w, Reaches Image.code v w ∧ (Dead Image.code w ∨ (w.pc = returnAddress v ∧ Preserves v w ∧
      StepR s v w (Within · (s.getReg .x2 - BitVec.ofNat 64 608) 24) ∧ Ctx s w k cnt P ∧
      ((w.getMem (s.getReg .x2 - BitVec.ofNat 64 608) = 0xffffffffffffffff ∧
          ∀ T, TranscriptAt s (s.getReg .x12) T → (prog bev s).run T = none) ∨
        (w.getMem (s.getReg .x2 - BitVec.ofNat 64 608) ≠ 0xffffffffffffffff ∧
          NewVecE v w (s.getReg .x2 - BitVec.ofNat 64 608)
            (vecEs w (s.getReg .x2 - BitVec.ofNat 64 608)) ∧
          Tracks (prog bev s) (s.getReg .x12) s w
            (K (vecEs w (s.getReg .x2 - BitVec.ofNat 64 608))))))) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have I := C.inv
  have pre : NextScalarsPre v := tpre hpre I (k := 608) (n := 24) (m := nextScalarsStack)
    (by omega) (by omega) (by omega) (by decide) (by decide) h10 h11
  obtain ⟨w, hrw, ⟨hpcw, hp, post⟩ | hd⟩ := hN.call (Reaches.refl v) hpc pre
  swap
  · exact ⟨w, hrw, Or.inl hd⟩
  have stT := TFrame.stepT hpre I (by decide) h10 h11 post.frame post.heap post.mono (hp.reg .x2)
  have st := stT.toR
  have C' := C.step hpre (st.weaken fun a ha ↦
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1])))))))
  refine ⟨w, hrw, Or.inr ⟨hpcw, hp, st, C', ?_⟩⟩
  by_cases hc : w.getMem (s.getReg .x2 - BitVec.ofNat 64 608) = 0xffffffffffffffff
  · refine Or.inl ⟨hc, htr.fail fun T hT ↦ ?_⟩
    have hv := post.value T (h11 ▸ hT)
    rw [h12, h10] at hv
    revert hv
    rcases (TM.nextScalars m).run T with _ | ⟨xs, T'⟩
    · exact fun _ ↦ rfl
    · intro hv
      obtain ⟨hne, -, -⟩ := hv
      exact absurd hc hne
  have hok (T : TState) (hT : TranscriptAt v (s.getReg .x12) T) : ∃ T',
      (TM.nextScalars m).run T = some (vecEs w (s.getReg .x2 - BitVec.ofNat 64 608), T') ∧
      NewVecE v w (s.getReg .x2 - BitVec.ofNat 64 608)
        (vecEs w (s.getReg .x2 - BitVec.ofNat 64 608)) ∧ TranscriptAt w (s.getReg .x12) T' := by
    have hv := post.value T (h11 ▸ hT)
    rw [h12, h10, h11] at hv
    revert hv
    rcases (TM.nextScalars m).run T with _ | ⟨xs, T'⟩
    · intro hv; exact absurd hv hc
    · intro hv
      obtain ⟨-, hx, hT'⟩ := hv
      have e : xs = vecEs w (s.getReg .x2 - BitVec.ofNat 64 608) := hx.elems.symm
      subst e
      exact ⟨T', rfl, hx, hT'⟩
  obtain ⟨T₀, -, hx₀, -⟩ := hok _ (canonT_at v (s.getReg .x12))
  exact Or.inr ⟨hc, hx₀, htr.bind fun T hT ↦ by
    obtain ⟨T', e, -, hT'⟩ := hok T hT
    exact ⟨T', e, hT'⟩⟩

/-- An `Err` of a `next_scalars`, through `0x80006c60`, `0x80006c68` or `0x80006c70`. -/
theorem errNs {bev : MachineState → Word → List E → Option E} {s t : MachineState} {k : Start}
    {cnt : E} {P : Word} (hpre : BusBalancePre s) (C : Ctx s t k cnt P)
    (hpc : t.pc = 0x80006c60 ∨ t.pc = 0x80006c68 ∨ t.pc = 0x80006c70)
    (hnone : ∀ T, TranscriptAt s (s.getReg .x12) T → (prog bev s).run T = none) :
    ∃ t', Reaches Image.code t t' ∧ Done bev s t' := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have sp := C.inv.sp
  have fin {t₁ : MachineState} (hm : ∀ a, t₁.getMem a = t.getMem a)
      (hsp : t₁.getReg .x2 = t.getReg .x2) (hpc₁ : t₁.pc = 0x80007100) :
      ∃ t', Reaches Image.code t₁ t' ∧ Done bev s t' :=
    err7100 hpre (C.inv.same hm hsp) (C.kept.step hpre (StepR.same hm C.inv.heap hsp)) hpc₁ hnone
  rcases hpc with hpc | hpc | hpc
  · obtain ⟨t₁, hr, h₁⟩ := Sym.BlockSpec.reaches b80006c60_spec hpc trivial
    obtain ⟨t', hr', hd⟩ := fin (b80006c60_mem_same h₁) (b80006c60_keeps h₁ .x2 (by decide))
      (b80006c60_pc h₁)
    exact ⟨t', hr.trans hr', hd⟩
  · obtain ⟨t₁, hr, h₁⟩ := Sym.BlockSpec.reaches b80006c68_spec hpc trivial
    obtain ⟨t', hr', hd⟩ := fin (b80006c68_mem_same h₁) (b80006c68_keeps h₁ .x2 (by decide))
      (b80006c68_pc h₁)
    exact ⟨t', hr.trans hr', hd⟩
  · obtain ⟨t₁, hr, h₁⟩ := Sym.BlockSpec.reaches b80006c70_spec hpc (by
      rv_eval [sp]
      valid_access hval [hb1])
    obtain ⟨t', hr', hd⟩ := fin (b80006c70_mem_same h₁) (b80006c70_keeps h₁ .x2 (by decide))
      (b80006c70_pc h₁)
    exact ⟨t', hr.trans hr', hd⟩

/-- A `Vec<E>`'s buffer and length, its capacity forgotten. -/
def HeapVec (s u : MachineState) (p l : Word) (xs : List E) : Prop := ∃ c, NewVecR s u c p l xs

theorem HeapVec.keepG {s v w : MachineState} {A : Word → Prop} (hpre : BusBalancePre s)
    (st : StepR s v w A) (hA : FrameW s A) {p l : Word} {xs : List E} (h : HeapVec s v p l xs) :
    HeapVec s w p l xs := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc.keepG hpre st hA⟩

theorem _root_.Rv64Verifier.Transcript.NewVecE.heapVec {s v w : MachineState} {a : Word} {xs : List E} (h : NewVecE v w a xs)
    (hm : heapNext s ≤ heapNext v) : HeapVec s w (vecPtr w a) (vecLen w a) xs := by
  have hb := h.buf
  simp only [NewBuf] at hb
  exact ⟨vecCap w a, h.vec.len, ⟨hb.1, hb.2.imp_right fun h' ↦ ⟨by omega, h'.2⟩⟩, h.elems⟩

/-- At the `checked` test: the children in registers, `x`'s capacity and length and the layer
count saved. -/
structure AtCk (s u w : MachineState) (k : Start) (cnt : E) (P : Word) (n : ℕ) (comb : E)
    (x : List E) (cl : E) (c0 c1 c2 : List E) : Prop where
  ctx : Ctx s w k cnt P
  regs : ∀ r ∈ ([.x9, .x20, .x24] : List Reg), w.getReg r = u.getReg r
  x19 : w.getReg .x19 = BitVec.ofNat 64 (2 ^ stepOf n)
  x22 : (w.getReg .x22).toNat = n % 2
  layers : (w.getMem (s.getReg .x2 - 1128)).toNat = n
  combAt : eAt w (s.getReg .x2 - BitVec.ofNat 64 128) = comb
  valuesPtr : w.getMem (s.getReg .x2 - 1280) = P
  xv : NewVecR s w (w.getMem (s.getReg .x2 - 1120)) (w.getReg .x8) (w.getMem (s.getReg .x2 - 1144)) x
  claimAt : eOf3 (w.getReg .x23) (w.getMem (s.getReg .x2 - 1208)) (w.getMem (s.getReg .x2 - 1216)) = cl
  ch0 : HeapVec s w (w.getReg .x27) (w.getReg .x18) c0
  ch1 : HeapVec s w (w.getReg .x26) (w.getReg .x21) c1
  ch2 : HeapVec s w (w.getMem (s.getReg .x2 - 1112)) (w.getReg .x25) c2
  step : StepR s u w (Scratch s)

/-- The three `next_scalars`, from the first's entry to the `checked` test. -/
theorem nsStep (hN : NextScalarsSpec) {bev : MachineState → Word → List E → Option E}
    {s u w₀ : MachineState} {k : Start} {cnt : E} {P : Word} {n : ℕ} {comb : E} {x : List E}
    {cl : E} {R : List E → List E → List E → TM BusResultRust} (hpre : BusBalancePre s)
    (h : AtNs s u w₀ k cnt P n comb x cl) (hpc : w₀.pc = 0x80004818)
    (hu : heapNext s ≤ heapNext u) (h9 : u.getReg .x9 = 0xffffffffffffffff)
    (h20 : u.getReg .x20 = s.getReg .x12) (h25 : (u.getReg .x25).toNat = n)
    (htr : Tracks (prog bev s) (s.getReg .x12) s w₀ (TM.nextScalars (2 ^ stepOf n) >>= fun c0 ↦
      TM.nextScalars (2 ^ stepOf n) >>= fun c1 ↦ TM.nextScalars (2 ^ stepOf n) >>= fun c2 ↦
        R c0 c1 c2)) :
    ∃ w, Reaches Image.code w₀ w ∧ (Done bev s w ∨ Dead Image.code w ∨ ∃ c0 c1 c2,
      w.pc = 0x80006844 ∧ AtCk s u w k cnt P n comb x cl c0 c1 c2 ∧
      Tracks (prog bev s) (s.getReg .x12) s w (R c0 c1 c2)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have C₀ := h.ctx
  have hm2 : (w₀.getReg .x12).toNat = 2 ^ stepOf n := by rw [h.x12]; exact pow_step_toNat n
  have e736 (v : MachineState) (hv : v.getReg .x2 = s.getReg .x2 - 1344) :
      v.getReg .x2 + 736 = s.getReg .x2 - BitVec.ofNat 64 608 := by
    rw [hv]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e744 (v : MachineState) (hv : v.getReg .x2 = s.getReg .x2 - 1344) :
      v.getReg .x2 + 744 = s.getReg .x2 - BitVec.ofNat 64 608 + 8 := by
    rw [hv]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e752 (v : MachineState) (hv : v.getReg .x2 = s.getReg .x2 - 1344) :
      v.getReg .x2 + 752 = s.getReg .x2 - BitVec.ofNat 64 608 + 16 := by
    rw [hv]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  -- the common frame
  let A : Word → Prop := fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 608) 24 ∨
    Within a (s.getReg .x2 - 1144) 8 ∨ Within a (s.getReg .x2 - 1128) 24
  have fA : FrameW s A := fun a ha ↦ by
    rcases ha with ha | ha | ha <;> addr_omega [ha, hb1]
  have sA (a : Word) (ha : A a) : Scratch s a := by
    rcases ha with ha | ha | ha
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1]))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1])))))
  have a608 (a : Word) (ha : Within a (s.getReg .x2 - BitVec.ofNat 64 608) 24) : A a := Or.inl ha
  -- first child
  obtain ⟨w₁, hr₁, hd | ⟨hpc₁, hp₁, st₁, C₁, res₁⟩⟩ :=
    nsCall hN hpre C₀ hpc h.x10 h.x11 hm2 htr
  · exact ⟨w₁, hr₁, Or.inr (Or.inl hd)⟩
  have sp₁ := C₁.inv.sp
  obtain ⟨w₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800067dc_spec
    (by rw [hpc₁, returnAddress_eq, h.x1]; decide) (by
      rv_eval [sp₁]
      and_intros <;> valid_access hval [hb1])
  have k₂ := b800067dc_keeps h₂
  have m₂ := b800067dc_mem_same h₂
  have st₂ : StepR s w₁ w₂ A := StepR.same m₂ C₁.inv.heap (k₂ .x2 (by decide))
  have C₂ := C₁.step hpre (st₂.weaken sA)
  have x9₁ : w₁.getReg .x9 = 0xffffffffffffffff := by
    rw [hp₁ .x9 (by decide), h.regs .x9 (by decide), h9]
  rcases res₁ with ⟨hc, hnone⟩ | ⟨hc₁, hv₁, htr₁⟩
  · obtain ⟨t, hrt, hdt⟩ := errNs hpre C₂
      (Or.inl (b800067dc_pc_taken h₂ (by rw [e736 _ sp₁, x9₁]; exact hc))) hnone
    exact ⟨t, hr₁.trans (hr₂.trans hrt), Or.inl hdt⟩
  have hpc₂ := b800067dc_pc_not_taken h₂ (by rw [e736 _ sp₁, x9₁]; exact hc₁)
  have sp₂ := C₂.inv.sp
  obtain ⟨w₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800067ec_spec hpc₂ (by
    rv_eval [sp₂]
    and_intros <;> valid_access hval [hb1])
  have k₃ := b800067ec_keeps h₃
  have fr₃ : DFrame w₂ w₃ fun a ↦ Within a (s.getReg .x2 - 1144) 8 ∨
      Within a (s.getReg .x2 - 1120) 8 := fun a ha ↦
    h₃.frame a (by
      rv_eval [sp₂]
      and_intros <;> intro he <;> exact ha 0 (by decide) (by
        rw [add_ofNat_zero, he]; addr_omega [hb1]))
  have st₃ : StepR s w₂ w₃ A :=
    StepR.ofDFrame C₂.inv.heap fr₃ (fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (by addr_omega [ha, hb1])))
      (fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hb1]) (k₃ .x2 (by decide))
  have C₃ := C₂.step hpre (st₃.weaken sA)
  have m200 := b800067ec_m_x2_200 h₃
  have m224 := b800067ec_m_x2_224 h₃
  rw [sp₂, show s.getReg .x2 - 1344 + 200 = s.getReg .x2 - 1144 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at m200
  rw [sp₂, show s.getReg .x2 - 1344 + 224 = s.getReg .x2 - 1120 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at m224
  -- second child
  obtain ⟨w₄, hr₄, hd | ⟨hpc₄, hp₄, st₄, C₄, res₄⟩⟩ :=
    nsCall hN hpre C₃ (b800067ec_pc h₃)
      (by rw [b800067ec_x10 h₃]; exact e736 _ sp₂)
      (by rw [b800067ec_x11 h₃, k₂ .x20 (by decide), hp₁ .x20 (by decide),
            h.regs .x20 (by decide), h20])
      (m := 2 ^ stepOf n)
      (by rw [b800067ec_x12 h₃, k₂ .x19 (by decide), hp₁ .x19 (by decide), h.x19, pow_step_toNat])
      (htr₁.keepF hpre C₁.inv C₃.inv.heap ((DFrame.of_same m₂ _).trans fr₃ fun _ h ↦ h) fun a ha ↦ by
        rcases ha with ha | ha <;> addr_omega [ha, hb1])
  · exact ⟨w₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr (Or.inl hd)⟩
  have sp₄ := C₄.inv.sp
  obtain ⟨w₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80006808_spec
    (by rw [hpc₄, returnAddress_eq, b800067ec_x1 h₃]; decide) (by
      rv_eval [sp₄]
      and_intros <;> valid_access hval [hb1])
  have k₅ := b80006808_keeps h₅
  have m₅ := b80006808_mem_same h₅
  have st₅ : StepR s w₄ w₅ A := StepR.same m₅ C₄.inv.heap (k₅ .x2 (by decide))
  have C₅ := C₄.step hpre (st₅.weaken sA)
  have x9₄ : w₄.getReg .x9 = 0xffffffffffffffff := by
    rw [hp₄ .x9 (by decide), k₃ .x9 (by decide), k₂ .x9 (by decide), x9₁]
  have hr05 := hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅)))
  rcases res₄ with ⟨hc, hnone⟩ | ⟨hc₄, hv₄, htr₄⟩
  · obtain ⟨t, hrt, hdt⟩ := errNs hpre C₅
      (Or.inr (Or.inl (b80006808_pc_taken h₅ (by rw [e736 _ sp₄, x9₄]; exact hc)))) hnone
    exact ⟨t, hr05.trans hrt, Or.inl hdt⟩
  have hpc₅ := b80006808_pc_not_taken h₅ (by rw [e736 _ sp₄, x9₄]; exact hc₄)
  have sp₅ := C₅.inv.sp
  obtain ⟨w₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80006818_spec hpc₅ (by
    rv_eval [sp₅]
    valid_access hval [hb1])
  have k₆ := b80006818_keeps h₆
  have fr₆ := b80006818_frame h₆ (by rw [sp₅]; addr_omega [hb1])
  rw [sp₅, show s.getReg .x2 - 1344 + 216 = s.getReg .x2 - 1128 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at fr₆
  have st₆ : StepR s w₅ w₆ A := StepR.ofMemFrame C₅.inv.heap fr₆
    (fun a ha ↦ Or.inr (Or.inr (by addr_omega [ha, hb1]))) (by addr_omega [hb1]) (k₆ .x2 (by decide))
  have C₆ := C₅.step hpre (st₆.weaken sA)
  have m216 := b80006818_m_x2_216 h₆
  rw [sp₅, show s.getReg .x2 - 1344 + 216 = s.getReg .x2 - 1128 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at m216
  -- third child
  obtain ⟨w₇, hr₇, hd | ⟨hpc₇, hp₇, st₇, C₇, res₇⟩⟩ :=
    nsCall hN hpre C₆ (b80006818_pc h₆)
      (by rw [b80006818_x10 h₆]; exact e736 _ sp₅)
      (by rw [b80006818_x11 h₆, k₅ .x20 (by decide), hp₄ .x20 (by decide), k₃ .x20 (by decide),
            k₂ .x20 (by decide), hp₁ .x20 (by decide), h.regs .x20 (by decide), h20])
      (m := 2 ^ stepOf n)
      (by rw [b80006818_x12 h₆, k₅ .x19 (by decide), hp₄ .x19 (by decide), k₃ .x19 (by decide),
            k₂ .x19 (by decide), hp₁ .x19 (by decide), h.x19, pow_step_toNat])
      (htr₄.keepF hpre C₄.inv C₆.inv.heap ((DFrame.of_same m₅ _).trans (DFrame.of_memFrame fr₆)
        fun _ h ↦ h) fun a ha ↦ by addr_omega [ha, hb1])
  · exact ⟨w₇, hr05.trans (hr₆.trans hr₇), Or.inr (Or.inl hd)⟩
  have sp₇ := C₇.inv.sp
  obtain ⟨w₈, hr₈, h₈⟩ := Sym.BlockSpec.reaches b80006830_spec
    (by rw [hpc₇, returnAddress_eq, b80006818_x1 h₆]; decide) (by
      rv_eval [sp₇]
      and_intros <;> valid_access hval [hb1])
  have k₈ := b80006830_keeps h₈
  have fr₈ := b80006830_frame h₈ (by rw [sp₇]; addr_omega [hb1])
  rw [sp₇, show s.getReg .x2 - 1344 + 232 = s.getReg .x2 - 1112 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at fr₈
  have st₈ : StepR s w₇ w₈ A := StepR.ofMemFrame C₇.inv.heap fr₈
    (fun a ha ↦ Or.inr (Or.inr (by addr_omega [ha, hb1]))) (by addr_omega [hb1]) (k₈ .x2 (by decide))
  have C₈ := C₇.step hpre (st₈.weaken sA)
  have x9₇ : w₇.getReg .x9 = 0xffffffffffffffff := by
    rw [hp₇ .x9 (by decide), k₆ .x9 (by decide), k₅ .x9 (by decide), x9₄]
  have hr08 := hr05.trans (hr₆.trans (hr₇.trans hr₈))
  rcases res₇ with ⟨hc, hnone⟩ | ⟨hc₇, hv₇, htr₇⟩
  · obtain ⟨t, hrt, hdt⟩ := errNs hpre C₈
      (Or.inr (Or.inr (b80006830_pc_taken h₈ (by rw [e736 _ sp₇, x9₇]; exact hc)))) hnone
    exact ⟨t, hr08.trans hrt, Or.inl hdt⟩
  have hpc₈ := b80006830_pc_not_taken h₈ (by rw [e736 _ sp₇, x9₇]; exact hc₇)
  -- the frames from each point on
  have g₆ (B : Word → Prop) (hB : ∀ a, Within a (s.getReg .x2 - 1128) 8 → B a) :
      StepR s w₅ w₆ B := StepR.ofMemFrame C₅.inv.heap fr₆ hB (by addr_omega [hb1]) (k₆ .x2 (by decide))
  have g₈ (B : Word → Prop) (hB : ∀ a, Within a (s.getReg .x2 - 1112) 8 → B a) :
      StepR s w₇ w₈ B := StepR.ofMemFrame C₇.inv.heap fr₈ hB (by addr_omega [hb1]) (k₈ .x2 (by decide))
  have g₅ : ∀ {B : Word → Prop}, StepR s w₄ w₅ B := StepR.same m₅ C₄.inv.heap (k₅ .x2 (by decide))
  let B₁ : Word → Prop := fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 608) 24 ∨
    Within a (s.getReg .x2 - 1128) 8 ∨ Within a (s.getReg .x2 - 1112) 8
  let B₂ : Word → Prop := fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 608) 24 ∨
    Within a (s.getReg .x2 - 1112) 8
  have tail₁ : StepR s w₃ w₈ B₁ := (st₄.weaken fun a ha ↦ Or.inl ha).join (g₅.join
    ((g₆ B₁ fun a ha ↦ Or.inr (Or.inl ha)).join ((st₇.weaken fun a ha ↦ Or.inl ha).join
      (g₈ B₁ fun a ha ↦ Or.inr (Or.inr ha)))))
  have tail₂ : StepR s w₆ w₈ B₂ :=
    (st₇.weaken fun a ha ↦ Or.inl ha).join (g₈ B₂ fun a ha ↦ Or.inr ha)
  have t6 : StepR s w₆ w₈ A := (st₇.weaken a608).join st₈
  have t5 : StepR s w₅ w₈ A := st₆.join t6
  have t3 : StepR s w₃ w₈ A := (st₄.weaken a608).join (st₅.join t5)
  have t2 : StepR s w₂ w₈ A := st₃.join t3
  have all : StepR s w₀ w₈ A := (st₁.weaken a608).join (st₂.join t2)
  have nA (j m : Nat) (hj : j = 128 ∧ m ≤ 24 ∨ (j = 1280 ∨ j = 1208 ∨ j = 1216) ∧ m ≤ 8)
      (y : Word) (hy : Within y (s.getReg .x2 - BitVec.ofNat 64 j) m) : ¬ A y := by
    intro hs
    rcases hs with hs | hs | hs <;> addr_omega [hy, hs, hb1, hj]
  -- registers
  have rg (r : Reg) (hr : r ∈ ([.x8, .x9, .x19, .x20, .x22, .x23, .x24] : List Reg)) :
      w₈.getReg r = w₀.getReg r := by
    rw [k₈ r (mem_of_mem hr _), hp₇ r (mem_of_mem hr _), k₆ r (mem_of_mem hr _),
      k₅ r (mem_of_mem hr _), hp₄ r (mem_of_mem hr _), k₃ r (mem_of_mem hr _),
      k₂ r (mem_of_mem hr _), hp₁ r (mem_of_mem hr _)]
  have rg₂ (r : Reg) (hr : r ∈ ([.x18, .x27] : List Reg)) : w₈.getReg r = w₂.getReg r := by
    rw [k₈ r (mem_of_mem hr _), hp₇ r (mem_of_mem hr _), k₆ r (mem_of_mem hr _),
      k₅ r (mem_of_mem hr _), hp₄ r (mem_of_mem hr _), k₃ r (mem_of_mem hr _)]
  have rg₅ (r : Reg) (hr : r ∈ ([.x21, .x26] : List Reg)) : w₈.getReg r = w₅.getReg r := by
    rw [k₈ r (mem_of_mem hr _), hp₇ r (mem_of_mem hr _), k₆ r (mem_of_mem hr _)]
  have m232 := b80006830_m_x2_232 h₈
  rw [sp₇, show s.getReg .x2 - 1344 + 232 = s.getReg .x2 - 1112 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 744 =
      s.getReg .x2 - BitVec.ofNat 64 608 + 8 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at m232
  have x25₈ := b80006830_x25 h₈
  rw [e752 _ sp₇] at x25₈
  -- the vectors
  have xs₀ : NewVecR s w₀ (w₀.getReg .x26) (w₀.getReg .x8) (w₀.getReg .x21) x := by
    have hx := h.xv
    have hb := hx.buf
    simp only [NewBuf] at hb
    exact ⟨hx.le, ⟨hb.1, hb.2.imp_right fun h' ↦ ⟨by omega, h'.2⟩⟩, hx.elems⟩
  have ch0 := (hv₁.heapVec C₀.inv.mono).keepG hpre ((StepR.same m₂ C₁.inv.heap
    (k₂ .x2 (by decide)) (A := A)).join t2) fA
  have ch1 := (hv₄.heapVec C₃.inv.mono).keepG hpre ((g₅ (B := A)).join t5) fA
  have ch2 := (hv₇.heapVec C₆.inv.mono).keepG hpre st₈ fA
  refine ⟨w₈, hr08, Or.inr (Or.inr ⟨_, _, _, hpc₈, {
    ctx := C₈
    regs := fun r hr ↦ by
      rw [rg r (mem_of_mem hr _)]; exact h.regs r (mem_of_mem hr _)
    x19 := by rw [rg .x19 (by decide)]; exact h.x19
    x22 := by rw [rg .x22 (by decide)]; exact h.x22
    layers := by
      rw [tail₂.word hpre (fun y hy hs ↦ by rcases hs with hs | hs <;> addr_omega [hy, hs, hb1])
        (Or.inl (by addr_omega [hb1])), m216, k₅ .x25 (by decide), hp₄ .x25 (by decide),
        k₃ .x25 (by decide), k₂ .x25 (by decide), hp₁ .x25 (by decide), h.regs .x25 (by decide), h25]
    combAt := by
      rw [all.eAtFrame hpre (by omega) (by omega) (nA 128 24 (by omega))]; exact h.combAt
    valuesPtr := by
      show w₈.getMem (s.getReg .x2 - BitVec.ofNat 64 1280) = P
      rw [all.word hpre (nA 1280 8 (by omega)) (Or.inl (by addr_omega [hb1]))]
      exact h.valuesPtr
    xv := by
      have hx := xs₀.keepG hpre all fA
      rw [tail₁.word hpre (fun y hy hs ↦ by rcases hs with hs | hs | hs <;> addr_omega [hy, hs, hb1])
          (Or.inl (by addr_omega [hb1])), m224,
        tail₁.word hpre (fun y hy hs ↦ by rcases hs with hs | hs | hs <;> addr_omega [hy, hs, hb1])
          (Or.inl (by addr_omega [hb1])), m200, rg .x8 (by decide), k₂ .x26 (by decide),
        hp₁ .x26 (by decide), k₂ .x21 (by decide), hp₁ .x21 (by decide)]
      exact hx
    claimAt := by
      show eOf3 _ (w₈.getMem (s.getReg .x2 - BitVec.ofNat 64 1208))
        (w₈.getMem (s.getReg .x2 - BitVec.ofNat 64 1216)) = cl
      rw [rg .x23 (by decide), all.word hpre (nA 1208 8 (by omega))
          (Or.inl (by addr_omega [hb1])),
        all.word hpre (nA 1216 8 (by omega)) (Or.inl (by addr_omega [hb1]))]
      exact h.claimAt
    ch0 := by
      rw [rg₂ .x27 (by decide), rg₂ .x18 (by decide), b800067dc_x27 h₂, b800067dc_x18 h₂,
        e744 _ sp₁, e752 _ sp₁]
      exact ch0
    ch1 := by
      rw [rg₅ .x26 (by decide), rg₅ .x21 (by decide), b80006808_x26 h₅, b80006808_x21 h₅,
        e744 _ sp₄, e752 _ sp₄]
      exact ch1
    ch2 := by rw [m232, x25₈]; exact ch2
    step := h.step.join (all.weaken sA) },
    htr₇.keepF hpre C₇.inv C₈.inv.heap (DFrame.of_memFrame fr₈) fun a ha ↦ by
      addr_omega [ha, hb1]⟩)⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
