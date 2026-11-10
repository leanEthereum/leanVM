import Rv64Verifier.Proofs.Gkr.KeccakCall

/-!
# `keccak::verify_keccak`: the twelve layers

Layer `0` on the first claim (`to_loop`, from `A11`), then the loop `0x80009320..0x80009374`
(`loop_step`) over layers `1..11`, the claim moved to `f + 296` after each; out of the loop at
`0x80009254` (`A12`), the last claim at `f + 296`. A layer's `Err` is returned.
-/

namespace Rv64Verifier.Gkr.Keccak
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F35
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

theorem K.block {s u v : MachineState} {first : KeccakClaim} {c : E} (hpre : VerifyKeccakPre s)
    (k : K s u first c) (hx2 : v.getReg .x2 = s.getReg .x2 - 5248) {rs : List (Nat × Nat)}
    (hok : SlotsOk rs = true) (h1 : SlotsSep rs 5216 8 = true) (h2 : SlotsSep rs 5200 24 = true)
    (h3 : SlotsSep rs 5072 120 = true) (F : DFrame u v (Slots s rs)) : K s v first c := by
  have hN := slots_next hpre hok F
  exact k.step hpre hx2
    ⟨by simp only [heapNext, hN]; exact k.base.heap.lo, by simp only [heapNext, hN]; exact k.base.heap.hi⟩
    (by simp only [heapNext, hN]; exact le_refl _) hok h1 h2 h3 (slots_sw F)

/-- A doubleword `J` bytes below the entry's `sp` that the step does not write. -/
theorem SW.word {s u v : MachineState} (hpre : VerifyKeccakPre s) (hH : HeapOk v)
    {rs : List (Nat × Nat)} {sp : Bool} (hok : SlotsOk rs = true) (F : DFrame u v (SW s u v rs sp))
    {J : Nat} (hJ : J ≤ 5248) (h8 : 8 ≤ J) (hsep : SlotsSep rs J 8 = true) {y : Word}
    (hy : y.toNat + J = (s.getReg .x2).toNat) : v.getMem y = u.getMem y := by
  have hb := bounds hpre
  rw [BitVec.eq_of_toNat_eq (x := y) (y := s.getReg .x2 - BitVec.ofNat 64 J)
    (by addr_omega [hb, hy, hJ])]
  exact SW.mem hpre hH hok hJ h8 hsep F

/-- After `memcpy(f + 320, f + 1976, 72)` and the header's stores: the claim returned at
`f + 1952` (at `t`, whose memory `u` keeps) is at `f + 296`. -/
theorem moved {s t u w v : MachineState} {first cl : KeccakClaim} {c : E}
    (hpre : VerifyKeccakPre s) (Ku : K s u first c) (htu : ∀ a, u.getMem a = t.getMem a)
    (hc : ClaimOut s t (s.getReg .x2 - 3296) cl) (x2w : w.getReg .x2 = s.getReg .x2 - 5248)
    (hNw : heapNext w = heapNext u) (F₅ : DFrame u w (SW s u w [(4928, 72)] false))
    (hcopy : ∀ j < 9, w.getMem (s.getReg .x2 - 4928 + BitVec.ofNat 64 (8 * j)) =
      u.getMem (s.getReg .x2 - 3272 + BitVec.ofNat 64 (8 * j)))
    (x2v : v.getReg .x2 = s.getReg .x2 - 5248) (F₆ : DFrame w v (Slots s [(4952, 24)]))
    (h0 : v.getMem (s.getReg .x2 - 4952) = t.getMem (s.getReg .x2 - 3296))
    (h8 : v.getMem (s.getReg .x2 - 4944) = t.getMem (s.getReg .x2 - 3288))
    (h16 : v.getMem (s.getReg .x2 - 4936) = t.getMem (s.getReg .x2 - 3280)) :
    K s v first c ∧ ClaimOut s v (s.getReg .x2 - 4952) cl ∧
      (∀ T, TranscriptAt t (s.getReg .x11) T → TranscriptAt v (s.getReg .x11) T) := by
  have hb := bounds hpre
  have B := Ku.base
  have hHw : HeapOk w := ⟨by rw [hNw]; exact B.heap.lo, by rw [hNw]; exact B.heap.hi⟩
  have hNw' : heapNext u ≤ heapNext w := le_of_eq hNw.symm
  have c₄ : ClaimOut s u (s.getReg .x2 - 3296) cl := Layer.claimOut_congr htu hc
  have c₅ := ClaimOut.step hpre B hHw hNw' (by decide) (J := 3296) (by decide) (by decide)
    (by decide) F₅ c₄
  have K₅ := Ku.step hpre x2w hHw hNw' (by decide) (by decide) (by decide) (by decide) F₅
  have K₆ := K₅.block hpre x2v (by decide) (by decide) (by decide) (by decide) F₆
  have hN₆ : heapNext v = heapNext w := by simp only [heapNext, slots_next hpre (by decide) F₆]
  have c₆ := ClaimOut.step hpre K₅.base K₆.base.heap (le_of_eq hN₆.symm) (by decide) (J := 3296)
    (by decide) (by decide) (by decide) (slots_sw F₆) c₅
  have F₄₆ : DFrame u v (SW s u v [(4928, 72), (4952, 24)] false) :=
    SW.trans F₅ (slots_sw F₆) (by simp) (by simp) (fun h ↦ h) (fun h ↦ h) hNw' (le_of_eq hN₆.symm)
  have kv (y : Word) (J : Nat) (hJ : J ≤ 5248) (h8 : 8 ≤ J)
      (hsep : SlotsSep [(4928, 72), (4952, 24)] J 8 = true) (hy : y.toNat + J = (s.getReg .x2).toNat) :
      v.getMem y = t.getMem y :=
    (SW.word hpre K₆.base.heap (by decide) F₄₆ hJ h8 hsep hy).trans (htu y)
  unfold verifyKeccakStack at hb
  have k0 := kv (s.getReg .x2 - 3296) 3296 (by decide) (by decide) (by decide) (by addr_omega [hb])
  have k8 := kv (s.getReg .x2 - 3288) 3288 (by decide) (by decide) (by decide) (by addr_omega [hb])
  have k16 := kv (s.getReg .x2 - 3280) 3280 (by decide) (by decide) (by decide) (by addr_omega [hb])
  refine ⟨K₆, stored hpre c₆ (by rw [h0, k0]) (by rw [h8, k8]) (by rw [h16, k16]) fun j hj ↦ ?_,
    fun T hT ↦ K₅.base.block_tat hpre (by decide) F₆
      (SW.tat hpre B hHw hNw' (by decide) F₅ (Layer.transcriptAt_congr htu hT))⟩
  have hs1 : SlotsSep [(4952, 24)] (4928 - 8 * j) 8 = true := by
    simp only [SlotsSep, List.all_cons, List.all_nil, Bool.and_true, Bool.or_eq_true,
      decide_eq_true_eq]
    omega
  have hs2 : SlotsSep [(4928, 72), (4952, 24)] (3272 - 8 * j) 8 = true := by
    simp only [SlotsSep, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      Bool.or_eq_true, decide_eq_true_eq]
    omega
  have hd : (s.getReg .x2 - 4928 + BitVec.ofNat 64 (8 * j)).toNat + (4928 - 8 * j) =
      (s.getReg .x2).toNat := by addr_omega [hb, hj]
  have hsr : (s.getReg .x2 - 3272 + BitVec.ofNat 64 (8 * j)).toNat + (3272 - 8 * j) =
      (s.getReg .x2).toNat := by addr_omega [hb, hj]
  rw [SW.word hpre K₆.base.heap (by decide) (slots_sw F₆) (by omega) (by omega) hs1 hd, hcopy j hj,
    htu, kv _ _ (by omega) (by omega) hs2 hsr]

/-! ## The states -/

/-- At the loop's head `0x80009320`, before layer `k`: the claim at `f + 296`. -/
structure L (s u : MachineState) (first : KeccakClaim) (c : E) (k : Nat) (cl : KeccakClaim) : Prop
    extends K s u first c where
  pc : u.pc = 0x80009320
  k1 : 1 ≤ k
  k12 : k < 12
  x8 : u.getReg .x8 = 0xffffffffffffffff
  x9 : u.getReg .x9 = s.getReg .x11
  x18 : u.getReg .x18 = s.getReg .x12
  x19 : u.getReg .x19 = 12
  x20 : u.getReg .x20 = 12
  x24 : u.getReg .x24 = 1
  x25 : u.getReg .x25 = s.getReg .x2 - 4928
  x26 : u.getReg .x26 = s.getReg .x2 - 3272
  x27 : u.getReg .x27 = BitVec.ofNat 64 k
  claim : ClaimOut s u (s.getReg .x2 - 4952) cl
  lens : Lens cl
  rest : Rest s u (kLayers (s.getReg .x12).toNat k cl >>=
    kTail (s.getReg .x12).toNat (instOf s) first c)

/-- Out of the loop at `0x80009254`: the last claim at `f + 296`, its `mu` in `s6`/`s7`. -/
structure A12 (s u : MachineState) (first : KeccakClaim) (c : E) (cl : KeccakClaim) : Prop
    extends K s u first c where
  pc : u.pc = 0x80009254
  x9 : u.getReg .x9 = s.getReg .x11
  x13 : u.getReg .x13 = 12
  x18 : u.getReg .x18 = s.getReg .x12
  x19 : u.getReg .x19 = 12
  x22 : u.getReg .x22 = vecPtr u (s.getReg .x2 - 4952)
  x23 : u.getReg .x23 = vecLen u (s.getReg .x2 - 4952)
  x24 : u.getReg .x24 = 1
  claim : ClaimOut s u (s.getReg .x2 - 4952) cl
  lens : Lens cl
  rest : Rest s u (kTail (s.getReg .x12).toNat (instOf s) first c cl)

theorem A11.toK {s u : MachineState} {seg lp : List E} {c : E} (hpre : VerifyKeccakPre s)
    (A : A11 s u seg lp c) : K s u (kFirst (instOf s) seg lp (outOf s) c) c := by
  have hb := bounds hpre
  have e24 : s.getReg .x2 - 5048 + 24 = s.getReg .x2 - 5024 :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have e48 : s.getReg .x2 - 5048 + 48 = s.getReg .x2 - 5000 :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have e72 : s.getReg .x2 - 5048 + 72 = s.getReg .x2 - 4976 :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have hseg : seg ≠ [] := List.ne_nil_of_length_pos (by rw [A.segLen]; exact Nat.one_pos)
  exact {
    base := A.base
    ok := A.ok
    m32 := A.m32
    m48 := A.m48
    m56 := A.m56
    m64 := A.m64
    firstV := ⟨by simp only [kFirst]; exact A.muV, by rw [e24]; simp only [kFirst]; exact A.pointV',
      by rw [e48]; simp only [kFirst]; exact A.weightsV, by
      rw [e72, A.value]; simp only [kFirst, lastOf]⟩
    firstLens := lens_first _ _ _ _ _ hseg
    committed := A.committed }

/-! ## An `Err` from a layer -/

theorem m48_of {s u : MachineState} {first : KeccakClaim} {c : E} (hpre : VerifyKeccakPre s)
    (k : K s u first c) (hx2 : u.getReg .x2 = s.getReg .x2 - 5248) :
    u.getMem (u.getReg .x2 + 48) = s.getReg .x10 := by
  have hb := bounds hpre
  rw [hx2, show s.getReg .x2 - 5248 + 48 = s.getReg .x2 - 5200 from
    BitVec.eq_of_toNat_eq (by addr_omega [hb])]
  exact k.m48

/-! ## The loop's body -/

theorem ofNat_succ (k : Nat) : BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [show (1 : Word).toNat = 1 from rfl]
  omega

theorem loop_step (hVL : VerifyLayerSpec) (hMC : Runtime.MemcpySpec 0x800126e4)
    {s u : MachineState} {first cl : KeccakClaim} {c : E} {k : Nat} (hpre : VerifyKeccakPre s)
    (A : L s u first c k cl) :
    ∃ v, Reaches Image.code u v ∧ ((∃ cl', L s v first c (k + 1) cl') ∨
      (∃ cl', A12 s v first c cl') ∨ Done s v) := by
  have hb := bounds hpre
  have B := A.base
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80009320_spec A.pc trivial
  have k₁ := b80009320_keeps h₁
  have m₁ := b80009320_mem_same h₁
  have x2₁ : u₁.getReg .x2 = s.getReg .x2 - 5248 := (k₁ .x2 (by decide)).trans B.x2
  have K₁ := A.toK.same hpre x2₁ m₁
  have c₁ := Layer.claimOut_congr m₁ A.claim
  have R₁ : Rest s u₁ (verifyLayerRust ⟨(s.getReg .x12).toNat, 12⟩ k cl >>= fun c' ↦
      kLayers (s.getReg .x12).toNat (k + 1) c' >>= kTail (s.getReg .x12).toNat (instOf s) first c) :=
    (A.rest.keep fun T hT ↦ Layer.transcriptAt_congr m₁ hT).congr (by
      rw [kLayers_succ _ _ A.k12, bind_assoc])
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 3296 := by rw [b80009320_x10 h₁, B.x2]; rv_eval []
  have x11₁ : u₁.getReg .x11 = s.getReg .x11 := by rw [b80009320_x11 h₁, A.x9]
  have x12₁ : u₁.getReg .x12 = s.getReg .x12 := by rw [b80009320_x12 h₁, A.x18]
  have x13₁ : u₁.getReg .x13 = 12 := by rw [b80009320_x13 h₁, A.x19]
  have x14₁ : u₁.getReg .x14 = BitVec.ofNat 64 k := by rw [b80009320_x14 h₁, A.x27]
  have x15₁ : u₁.getReg .x15 = s.getReg .x2 - BitVec.ofNat 64 4952 := by
    rw [b80009320_x15 h₁, B.x2]; exact BitVec.eq_of_toNat_eq (by addr_omega [hb])
  obtain ⟨t, hr₂, hd | ⟨hpc₂, hpres₂, K₂, -, hres⟩⟩ := layer_call hVL hpre K₁ (b80009320_pc h₁)
    (J := 4952) (by decide) (by decide) (by decide) c₁ A.lens x10₁ x11₁ x12₁ x13₁ x14₁ A.k12 x15₁ R₁
  · exact ⟨t, hr₁.trans hr₂, Or.inr (Or.inr (Or.inr hd))⟩
  have x2t : t.getReg .x2 = s.getReg .x2 - 5248 := (hpres₂.reg .x2).trans x2₁
  have pct : t.pc = 0x80009340 := by rw [hpc₂, returnAddress_eq, b80009320_x1 h₁]; decide
  have x8t : t.getReg .x8 = 0xffffffffffffffff := by rw [hpres₂.reg .x8, k₁ .x8 (by decide), A.x8]
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80009340_spec pct (by
    rv_eval [x2t]
    valid_access hpre.stack.valid [hb])
  have k₃ := b80009340_keeps h₃
  have m₃ := b80009340_mem_same h₃
  have x2₃ : u₃.getReg .x2 = s.getReg .x2 - 5248 := (k₃ .x2 (by decide)).trans x2t
  have tag : t.getMem (t.getReg .x2 + 1952) = t.getMem (s.getReg .x2 - 3296) := by
    rw [x2t]; exact congrArg _ (BitVec.eq_of_toNat_eq (by addr_omega [hb]))
  have K₃ := K₂.same hpre x2₃ m₃
  rcases hres with ⟨hcap, hfails⟩ | ⟨hcap, c', hc', hl', hR'⟩
  · -- `Err`
    have pc₃ := b80009340_pc_taken h₃ (by rw [tag, hcap, x8t]; rfl)
    have ho := hpre.out
    have m48 := m48_of hpre K₃ x2₃
    have m48' := K₃.m48
    obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80009388_spec pc₃ (by
      rv_eval [x2₃]
      rv_eval [m48']
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
    have f₄ : MemFrame u₃ u₄ (s.getReg .x10) 24 := h₄.memFrame (by
      intro w hw
      simp only [b80009388, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> rv_eval [m48] <;> addr_omega [ho])
    have hcap₄ := b80009388_m2 h₄
    rw [m48] at hcap₄
    obtain ⟨v, hr₅, hv⟩ := err_exit hpre K₃.base (b80009388_pc h₄)
      ((b80009388_keeps h₄ .x2 (by decide)).trans x2₃) f₄ hcap₄ hfails
    exact ⟨v, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inr (Or.inr hv)⟩
  -- `Ok`: the claim to `f + 296`
  have pc₃ := b80009340_pc_not_taken h₃ (by rw [tag, x8t]; exact hcap)
  have x21₃ : u₃.getReg .x21 = t.getMem (s.getReg .x2 - 3296) := by rw [b80009340_x21 h₃, tag]
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80009348_spec pc₃ (by
    rv_eval [x2₃]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₄ := b80009348_keeps h₄
  have m₄ := b80009348_mem_same h₄
  have x2₄ : u₄.getReg .x2 = s.getReg .x2 - 5248 := (k₄ .x2 (by decide)).trans x2₃
  have K₄ := K₃.same hpre x2₄ m₄
  have m34 : ∀ a, u₄.getMem a = t.getMem a := fun a ↦ by rw [m₄, m₃]
  have x10₄ : u₄.getReg .x10 = s.getReg .x2 - 4928 := by
    rw [b80009348_x10 h₄, k₃ .x25 (by decide), hpres₂.reg .x25, k₁ .x25 (by decide), A.x25]
  have x11₄ : u₄.getReg .x11 = s.getReg .x2 - 3272 := by
    rw [b80009348_x11 h₄, k₃ .x26 (by decide), hpres₂.reg .x26, k₁ .x26 (by decide), A.x26]
  obtain ⟨w, hr₅, hd | ⟨hpc₅, hpres₅, F₅, hN₅, hcopy⟩⟩ := memcpy_72 hMC hpre K₄.base
    (b80009348_pc h₄) x10₄ x11₄ (b80009348_x12 h₄)
  · exact ⟨w, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inr (Or.inr (Or.inr hd))⟩
  have x2₅ : w.getReg .x2 = s.getReg .x2 - 5248 := (hpres₅.reg .x2).trans x2₄
  obtain ⟨v, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80009368_spec
    (by rw [hpc₅, returnAddress_eq, b80009348_x1 h₄]; decide) (by
      rv_eval [x2₅]
      and_intros <;> valid_access hpre.stack.valid [hb])
  have k₆ := b80009368_keeps h₆
  have x2₆ : v.getReg .x2 = s.getReg .x2 - 5248 := (k₆ .x2 (by decide)).trans x2₅
  have F₆ : DFrame w v (Slots s [(4952, 24)]) := by
    have f := b80009368_frame h₆ (by rw [x2₅]; addr_omega [hb])
    rw [x2₅] at f
    rv_eval [] at f
    exact (DFrame.of_memFrame f).mono fun a ha ↦ ⟨(4952, 24), List.mem_singleton_self _, ha⟩
  have a2 (n : Nat) (hn : n ≤ 5248) :
      w.getReg .x2 + BitVec.ofNat 64 n = s.getReg .x2 - BitVec.ofNat 64 (5248 - n) := by
    rw [x2₅]; exact BitVec.eq_of_toNat_eq (by addr_omega [hb, hn])
  have h0 : v.getMem (s.getReg .x2 - 4952) = t.getMem (s.getReg .x2 - 3296) := by
    rw [← show w.getReg .x2 + 296 = s.getReg .x2 - 4952 from a2 296 (by decide),
      b80009368_m_x2_296 h₆, hpres₅.reg .x21, k₄ .x21 (by decide), x21₃]
  have h8 : v.getMem (s.getReg .x2 - 4944) = t.getMem (s.getReg .x2 - 3288) := by
    rw [← show w.getReg .x2 + 304 = s.getReg .x2 - 4944 from a2 304 (by decide),
      b80009368_m_x2_304 h₆, hpres₅.reg .x22, b80009348_x22 h₄, x2₃, m₃]
    exact congrArg _ (BitVec.eq_of_toNat_eq (by addr_omega [hb]))
  have h16 : v.getMem (s.getReg .x2 - 4936) = t.getMem (s.getReg .x2 - 3280) := by
    rw [← show w.getReg .x2 + 312 = s.getReg .x2 - 4936 from a2 312 (by decide),
      b80009368_m_x2_312 h₆, hpres₅.reg .x23, b80009348_x23 h₄, x2₃, m₃]
    exact congrArg _ (BitVec.eq_of_toNat_eq (by addr_omega [hb]))
  obtain ⟨K₆, c₆, tat⟩ := moved hpre K₄ m34 hc' x2₅ hN₅ F₅ hcopy x2₆ F₆ h0 h8 h16
  have R₆ := hR'.keep tat
  have hr : Reaches Image.code u v :=
    hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₆))))
  have y8 : v.getReg .x8 = 0xffffffffffffffff := by
    rw [k₆ .x8 (by decide), hpres₅.reg .x8, k₄ .x8 (by decide), k₃ .x8 (by decide), x8t]
  have y9 : v.getReg .x9 = s.getReg .x11 := by
    rw [k₆ .x9 (by decide), hpres₅.reg .x9, k₄ .x9 (by decide), k₃ .x9 (by decide),
      hpres₂.reg .x9, k₁ .x9 (by decide), A.x9]
  have y18 : v.getReg .x18 = s.getReg .x12 := by
    rw [k₆ .x18 (by decide), hpres₅.reg .x18, k₄ .x18 (by decide), k₃ .x18 (by decide),
      hpres₂.reg .x18, k₁ .x18 (by decide), A.x18]
  have y19 : v.getReg .x19 = 12 := by
    rw [k₆ .x19 (by decide), hpres₅.reg .x19, k₄ .x19 (by decide), k₃ .x19 (by decide),
      hpres₂.reg .x19, k₁ .x19 (by decide), A.x19]
  have y20 : v.getReg .x20 = 12 := by
    rw [k₆ .x20 (by decide), hpres₅.reg .x20, k₄ .x20 (by decide), k₃ .x20 (by decide),
      hpres₂.reg .x20, k₁ .x20 (by decide), A.x20]
  have y24 : v.getReg .x24 = 1 := by
    rw [k₆ .x24 (by decide), hpres₅.reg .x24, k₄ .x24 (by decide), k₃ .x24 (by decide),
      hpres₂.reg .x24, k₁ .x24 (by decide), A.x24]
  have y25 : v.getReg .x25 = s.getReg .x2 - 4928 := by
    rw [k₆ .x25 (by decide), hpres₅.reg .x25, k₄ .x25 (by decide), k₃ .x25 (by decide),
      hpres₂.reg .x25, k₁ .x25 (by decide), A.x25]
  have y26 : v.getReg .x26 = s.getReg .x2 - 3272 := by
    rw [k₆ .x26 (by decide), hpres₅.reg .x26, k₄ .x26 (by decide), k₃ .x26 (by decide),
      hpres₂.reg .x26, k₁ .x26 (by decide), A.x26]
  have y27 : v.getReg .x27 = BitVec.ofNat 64 (k + 1) := by
    rw [k₆ .x27 (by decide), hpres₅.reg .x27, b80009348_x27 h₄, k₃ .x27 (by decide),
      hpres₂.reg .x27, k₁ .x27 (by decide), A.x27, ofNat_succ k]
  have w20 : w.getReg .x20 = 12 := (k₆ .x20 (by decide)).symm.trans y20
  have w27 : w.getReg .x27 = BitVec.ofNat 64 (k + 1) := (k₆ .x27 (by decide)).symm.trans y27
  by_cases hk : k + 1 < 12
  · have pc₆ := b80009368_pc_taken h₆ (by
      rw [w20, w27]
      intro h
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, show (12 : Word).toNat = 12 from rfl] at this
      omega)
    exact ⟨v, hr, Or.inl ⟨c', { K₆ with
      pc := pc₆
      k1 := by omega
      k12 := hk
      x8 := y8
      x9 := y9
      x18 := y18
      x19 := y19
      x20 := y20
      x24 := y24
      x25 := y25
      x26 := y26
      x27 := y27
      claim := c₆
      lens := hl'
      rest := R₆ }⟩⟩
  have hk12 : k + 1 = 12 := by have := A.k12; omega
  have pc₆ := b80009368_pc_not_taken h₆ (by rw [w20, w27, hk12]; rfl)
  obtain ⟨v₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80009378_spec pc₆ trivial
  have k₇ := b80009378_keeps h₇
  have m₇ := b80009378_mem_same h₇
  have pc₇ := b80009378_pc_not_taken h₇ (by rw [y19]; decide)
  obtain ⟨v₈, hr₈, h₈⟩ := Sym.BlockSpec.reaches b80009380_spec pc₇ trivial
  have k₈ := b80009380_keeps h₈
  have m₈ := b80009380_mem_same h₈
  have m68 : ∀ a, v₈.getMem a = v.getMem a := fun a ↦ by rw [m₈, m₇]
  have x2₈ : v₈.getReg .x2 = s.getReg .x2 - 5248 := by
    rw [k₈ .x2 (by decide), k₇ .x2 (by decide), x2₆]
  have hb8 : s.getReg .x2 - 4952 + 8 = s.getReg .x2 - 4944 :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have hb16 : s.getReg .x2 - 4952 + 16 = s.getReg .x2 - 4936 :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb])
  refine ⟨v₈, hr.trans (hr₇.trans hr₈), Or.inr (Or.inl ⟨c', { K₆.same hpre x2₈ m68 with
    pc := b80009380_pc h₈
    x9 := by rw [k₈ .x9 (by decide), k₇ .x9 (by decide), y9]
    x13 := by rw [b80009380_x13 h₈, k₇ .x19 (by decide), y19]
    x18 := by rw [k₈ .x18 (by decide), k₇ .x18 (by decide), y18]
    x19 := by rw [k₈ .x19 (by decide), k₇ .x19 (by decide), y19]
    x22 := by
      rw [k₈ .x22 (by decide), k₇ .x22 (by decide), k₆ .x22 (by decide)]
      simp only [vecPtr]
      rw [m68, hb8, ← show w.getReg .x2 + 304 = s.getReg .x2 - 4944 from a2 304 (by decide),
        b80009368_m_x2_304 h₆]
    x23 := by
      rw [k₈ .x23 (by decide), k₇ .x23 (by decide), k₆ .x23 (by decide)]
      simp only [vecLen]
      rw [m68, hb16, ← show w.getReg .x2 + 312 = s.getReg .x2 - 4936 from a2 312 (by decide),
        b80009368_m_x2_312 h₆]
    x24 := by rw [k₈ .x24 (by decide), k₇ .x24 (by decide), y24]
    claim := Layer.claimOut_congr m68 c₆
    lens := hl'
    rest := (R₆.keep fun T hT ↦ Layer.transcriptAt_congr m68 hT).congr (by
      rw [hk12, kLayers_end, pure_bind]) }⟩)⟩

/-- The loop, from layer `k` on. -/
theorem loop (hVL : VerifyLayerSpec) (hMC : Runtime.MemcpySpec 0x800126e4) {s : MachineState}
    {first : KeccakClaim} {c : E} (hpre : VerifyKeccakPre s) :
    ∀ n k u cl, 12 - k = n → L s u first c k cl →
      ∃ v, Reaches Image.code u v ∧ ((∃ cl', A12 s v first c cl') ∨ Done s v) := by
  intro n
  induction n with
  | zero => intro k u cl hn A; have := A.k12; omega
  | succ n ih =>
    intro k u cl hn A
    obtain ⟨v, hr, ⟨cl', A'⟩ | ⟨cl', A'⟩ | hd⟩ := loop_step hVL hMC hpre A
    · obtain ⟨t, hr', ht⟩ := ih (k + 1) v cl' (by omega) A'
      exact ⟨t, hr.trans hr', ht⟩
    · exact ⟨v, hr, Or.inl ⟨cl', A'⟩⟩
    · exact ⟨v, hr, Or.inr hd⟩

/-! ## Layer `0` -/

theorem to_loop (hVL : VerifyLayerSpec) (hMC : Runtime.MemcpySpec 0x800126e4) {s u : MachineState}
    {seg lp : List E} {c : E} (hpre : VerifyKeccakPre s) (A : A11 s u seg lp c) :
    ∃ v, Reaches Image.code u v ∧
      ((∃ cl, L s v (kFirst (instOf s) seg lp (outOf s) c) c 1 cl) ∨ Done s v) := by
  have hb := bounds hpre
  have K₀ := A11.toK hpre A
  have B := A.base
  obtain ⟨t, hr₂, hd | ⟨hpc₂, hpres₂, K₂, -, hres⟩⟩ := layer_call hVL hpre K₀ A.pc (J := 5048) (k := 0)
    (f := kLayered (s.getReg .x12).toNat (instOf s) (kFirst (instOf s) seg lp (outOf s) c) c)
    (by decide) (by decide) (by decide) K₀.firstV K₀.firstLens A.x10 A.x11 A.x12 A.x13 A.x14
    (by decide) A.x15 A.rest
  · exact ⟨t, hr₂, Or.inr (Or.inr hd)⟩
  have x2t : t.getReg .x2 = s.getReg .x2 - 5248 := (hpres₂.reg .x2).trans B.x2
  have pct : t.pc = 0x80009214 := by rw [hpc₂, returnAddress_eq, A.x1]; decide
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80009214_spec pct (by
    rv_eval [x2t]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₃ := b80009214_keeps h₃
  have m₃ := b80009214_mem_same h₃
  have x2₃ : u₃.getReg .x2 = s.getReg .x2 - 5248 := (k₃ .x2 (by decide)).trans x2t
  have tag (n : Nat) (hn : n ≤ 5248) :
      t.getMem (t.getReg .x2 + BitVec.ofNat 64 n) = t.getMem (s.getReg .x2 - BitVec.ofNat 64 (5248 - n)) := by
    rw [x2t]; exact congrArg _ (BitVec.eq_of_toNat_eq (by addr_omega [hb, hn]))
  have t1952 : t.getMem (t.getReg .x2 + 1952) = t.getMem (s.getReg .x2 - 3296) := tag 1952 (by decide)
  have t1960 : t.getMem (t.getReg .x2 + 1960) = t.getMem (s.getReg .x2 - 3288) := tag 1960 (by decide)
  have t1968 : t.getMem (t.getReg .x2 + 1968) = t.getMem (s.getReg .x2 - 3280) := tag 1968 (by decide)
  have K₃ := K₂.same hpre x2₃ m₃
  rcases hres with ⟨hcap, hfails⟩ | ⟨hcap, c', hc', hl', hR'⟩
  · -- `Err`
    have pc₃ := b80009214_pc_taken h₃ (by rw [t1952, hcap]; rfl)
    have ho := hpre.out
    have m48 := m48_of hpre K₃ x2₃
    have m48' := K₃.m48
    obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800092f0_spec pc₃ (by
      rv_eval [x2₃]
      rv_eval [m48']
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
    have f₄ : MemFrame u₃ u₄ (s.getReg .x10) 24 := h₄.memFrame (by
      intro w hw
      simp only [b800092f0, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> rv_eval [m48] <;> addr_omega [ho])
    have hcap₄ := b800092f0_m2 h₄
    rw [m48, b80009214_x10 h₃] at hcap₄
    obtain ⟨v, hr₅, hv⟩ := err_exit hpre K₃.base (b800092f0_pc h₄)
      ((b800092f0_keeps h₄ .x2 (by decide)).trans x2₃) f₄ hcap₄ hfails
    exact ⟨v, hr₂.trans (hr₃.trans (hr₄.trans hr₅)), Or.inr hv⟩
  -- `Ok`: the claim to `f + 296`
  have pc₃ := b80009214_pc_not_taken h₃ (by rw [t1952]; exact hcap)
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80009228_spec pc₃ trivial
  have k₄ := b80009228_keeps h₄
  have m₄ := b80009228_mem_same h₄
  have x2₄ : u₄.getReg .x2 = s.getReg .x2 - 5248 := (k₄ .x2 (by decide)).trans x2₃
  have K₄ := K₃.same hpre x2₄ m₄
  have m34 : ∀ a, u₄.getMem a = t.getMem a := fun a ↦ by rw [m₄, m₃]
  have x10₄ : u₄.getReg .x10 = s.getReg .x2 - 4928 := by rw [b80009228_x10 h₄, x2₃]; rv_eval []
  have x11₄ : u₄.getReg .x11 = s.getReg .x2 - 3272 := by rw [b80009228_x11 h₄, x2₃]; rv_eval []
  obtain ⟨w, hr₅, hd | ⟨hpc₅, hpres₅, F₅, hN₅, hcopy⟩⟩ := memcpy_72 hMC hpre K₄.base
    (b80009228_pc h₄) x10₄ x11₄ (b80009228_x12 h₄)
  · exact ⟨w, hr₂.trans (hr₃.trans (hr₄.trans hr₅)), Or.inr (Or.inr hd)⟩
  have x2₅ : w.getReg .x2 = s.getReg .x2 - 5248 := (hpres₅.reg .x2).trans x2₄
  obtain ⟨v, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80009240_spec
    (by rw [hpc₅, returnAddress_eq, b80009228_x1 h₄]; decide) (by
      rv_eval [x2₅]
      and_intros <;> valid_access hpre.stack.valid [hb])
  have k₆ := b80009240_keeps h₆
  have x2₆ : v.getReg .x2 = s.getReg .x2 - 5248 := (k₆ .x2 (by decide)).trans x2₅
  have F₆ : DFrame w v (Slots s [(4952, 24)]) := by
    have f := b80009240_frame h₆ (by rw [x2₅]; addr_omega [hb])
    rw [x2₅] at f
    rv_eval [] at f
    exact (DFrame.of_memFrame f).mono fun a ha ↦ ⟨(4952, 24), List.mem_singleton_self _, ha⟩
  have a2 (n : Nat) (hn : n ≤ 5248) :
      w.getReg .x2 + BitVec.ofNat 64 n = s.getReg .x2 - BitVec.ofNat 64 (5248 - n) := by
    rw [x2₅]; exact BitVec.eq_of_toNat_eq (by addr_omega [hb, hn])
  have h0 : v.getMem (s.getReg .x2 - 4952) = t.getMem (s.getReg .x2 - 3296) := by
    rw [← show w.getReg .x2 + 296 = s.getReg .x2 - 4952 from a2 296 (by decide),
      b80009240_m_x2_296 h₆, hpres₅.reg .x8, k₄ .x8 (by decide), b80009214_x8 h₃, t1952]
  have h8 : v.getMem (s.getReg .x2 - 4944) = t.getMem (s.getReg .x2 - 3288) := by
    rw [← show w.getReg .x2 + 304 = s.getReg .x2 - 4944 from a2 304 (by decide),
      b80009240_m_x2_304 h₆, hpres₅.reg .x22, k₄ .x22 (by decide), b80009214_x22 h₃, t1960]
  have h16 : v.getMem (s.getReg .x2 - 4936) = t.getMem (s.getReg .x2 - 3280) := by
    rw [← show w.getReg .x2 + 312 = s.getReg .x2 - 4936 from a2 312 (by decide),
      b80009240_m_x2_312 h₆, hpres₅.reg .x23, k₄ .x23 (by decide), b80009214_x23 h₃, t1968]
  obtain ⟨K₆, c₆, tat⟩ := moved hpre K₄ m34 hc' x2₅ hN₅ F₅ hcopy x2₆ F₆ h0 h8 h16
  have y19 : v.getReg .x19 = 12 := by
    rw [k₆ .x19 (by decide), hpres₅.reg .x19, k₄ .x19 (by decide), k₃ .x19 (by decide),
      hpres₂.reg .x19, A.x19]
  have pc₆ := b80009240_pc_taken h₆ (by rw [← k₆ .x19 (by decide), y19]; decide)
  obtain ⟨v₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80009304_spec pc₆ trivial
  have k₇ := b80009304_keeps h₇
  have m₇ := b80009304_mem_same h₇
  have pc₇ := b80009304_pc_taken h₇ (by rw [y19]; decide)
  obtain ⟨v₈, hr₈, h₈⟩ := Sym.BlockSpec.reaches b80009314_spec pc₇ trivial
  have k₈ := b80009314_keeps h₈
  have m₈ := b80009314_mem_same h₈
  have m68 : ∀ a, v₈.getMem a = v.getMem a := fun a ↦ by rw [m₈, m₇]
  have x2₈ : v₈.getReg .x2 = s.getReg .x2 - 5248 := by
    rw [k₈ .x2 (by decide), k₇ .x2 (by decide), x2₆]
  have hr : Reaches Image.code u v₈ :=
    hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans (hr₆.trans (hr₇.trans hr₈)))))
  refine ⟨v₈, hr, Or.inl ⟨c', { K₆.same hpre x2₈ m68 with
    pc := b80009314_pc h₈
    k1 := le_refl _
    k12 := by decide
    x8 := b80009314_x8 h₈
    x9 := by
      rw [k₈ .x9 (by decide), k₇ .x9 (by decide), k₆ .x9 (by decide), hpres₅.reg .x9,
        k₄ .x9 (by decide), k₃ .x9 (by decide), hpres₂.reg .x9, A.x9]
    x18 := by
      rw [k₈ .x18 (by decide), k₇ .x18 (by decide), k₆ .x18 (by decide), hpres₅.reg .x18,
        k₄ .x18 (by decide), k₃ .x18 (by decide), hpres₂.reg .x18, A.x18]
    x19 := by rw [k₈ .x19 (by decide), k₇ .x19 (by decide), y19]
    x20 := by rw [k₈ .x20 (by decide), b80009304_x20 h₇, y19]
    x24 := by
      rw [k₈ .x24 (by decide), k₇ .x24 (by decide), k₆ .x24 (by decide), hpres₅.reg .x24,
        k₄ .x24 (by decide), k₃ .x24 (by decide), hpres₂.reg .x24, A.x24]
    x25 := by
      rw [k₈ .x25 (by decide), k₇ .x25 (by decide), k₆ .x25 (by decide), hpres₅.reg .x25,
        b80009228_x25 h₄, x2₃]
      rv_eval []
    x26 := by rw [b80009314_x26 h₈, k₇ .x2 (by decide), x2₆]; rv_eval []
    x27 := b80009314_x27 h₈
    claim := Layer.claimOut_congr m68 c₆
    lens := hl'
    rest := (hR'.keep tat).keep fun T hT ↦ Layer.transcriptAt_congr m68 hT }⟩⟩

end Rv64Verifier.Gkr.Keccak
