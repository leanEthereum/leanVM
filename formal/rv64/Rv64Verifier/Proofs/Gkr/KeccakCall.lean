import Rv64Verifier.Proofs.Gkr.KeccakClaim

/-!
# `keccak::verify_keccak`: a call to `verify_layer`, the claim it returns moved to `f + 296`

What the layers' loop keeps (`K`): the spills, the first claim at `f + 200`, the committed value.
A claim's `Vec`s are never empty (`Lens`): the mirror's layer keeps the point's length, and the
first claim's are explicit. `layer_call` is a call to `verify_layer` with the claim at `f + 200` or
`f + 296`, its result at `f + 1952`; `memcpy_72` and `stored` move that result to `f + 296`.
-/

namespace Rv64Verifier.Gkr.Keccak
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F35
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-! ## Non-empty claims -/

/-- The claim's three `Vec`s are not empty. -/
def Lens (c : KeccakClaim) : Prop := c.mu ≠ [] ∧ c.point ≠ [] ∧ c.weights ≠ []

theorem run_bind_inv {α β : Type} {m : TM α} {f : α → TM β} {T : TState} {r : β × TState}
    (h : (m >>= f).run T = some r) : ∃ a T₁, m.run T = some (a, T₁) ∧ (f a).run T₁ = some r := by
  rw [StateT.run_bind] at h
  rcases hm : m.run T with _ | ⟨a, T₁⟩
  · rw [hm] at h; exact absurd h (by simp)
  · rw [hm] at h; exact ⟨a, T₁, rfl, h⟩

theorem run_pure_inv {α : Type} {x a : α} {T T' : TState} (h : (pure x : TM α).run T = some (a, T')) :
    x = a := (Prod.mk.inj (Option.some.inj h)).1

theorem packRound_len {acc a : E × E × List E} {r : E} {T T' : TState}
    (h : (packRound acc r).run T = some (a, T')) : a.2.2.length = acc.2.2.length + 1 := by
  unfold packRound at h
  obtain ⟨m, T₁, -, h⟩ := run_bind_inv h
  obtain ⟨c, T₂, -, h⟩ := run_bind_inv h
  rw [← run_pure_inv h, List.length_append, List.length_singleton]

theorem foldlM_packRound_len : ∀ (rs : List E) (acc : E × E × List E) {T T' : TState}
    {a : E × E × List E}, (rs.foldlM packRound acc).run T = some (a, T') →
      a.2.2.length = acc.2.2.length + rs.length
  | [], acc, T, T', a, h => by
    rw [List.foldlM_nil] at h
    rw [← run_pure_inv h, List.length_nil, Nat.add_zero]
  | r :: rs, acc, T, T', a, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨b, T₁, h1, h2⟩ := run_bind_inv h
    rw [foldlM_packRound_len rs b h2, packRound_len h1, List.length_cons]; omega

/-- The mirror's layer returns a non-empty claim from one whose point is not empty. -/
theorem lens_layer {shape : KeccakShape} {step : Nat} {cl c : KeccakClaim} {T T' : TState}
    (hl : cl.point ≠ []) (h : (verifyLayerRust shape step cl).run T = some (c, T')) : Lens c := by
  rw [Layer.verifyLayerRust_eq] at h
  obtain ⟨product, T₁, -, h⟩ := run_bind_inv h
  rw [Layer.run_require] at h
  split_ifs at h
  unfold Layer.stage2 at h
  obtain ⟨sv, T₂, -, h⟩ := run_bind_inv h
  unfold Layer.packRest at h
  obtain ⟨acc, T₃, hacc, h⟩ := run_bind_inv h
  have hlen := foldlM_packRound_len _ _ hacc
  rw [Layer.stage4_eq] at h
  obtain ⟨lv, T₄, -, h⟩ := run_bind_inv h
  unfold Layer.stage5 at h
  obtain ⟨t, T₅, -, h⟩ := run_bind_inv h
  rw [Layer.run_require] at h
  split_ifs at h
  unfold Layer.stage7 at h
  obtain ⟨beta, T₆, -, h⟩ := run_bind_inv h
  rw [← run_pure_inv h]
  refine ⟨?_, ?_, ?_⟩
  · simp [instanceWeightsRust, rmfeEmbedRust]
  · intro h0
    dsimp only at h0 hlen
    rw [h0, List.length_nil, List.drop_zero] at hlen
    exact hl (List.length_eq_zero_iff.mp (by omega))
  · simp [linearTransposeRust, keccakBits]

theorem lens_first (inst seg lp output : List E) (c : E) (hs : seg ≠ []) :
    Lens (kFirst inst seg lp output c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := congrArg List.length h
    dsimp only [kFirst] at this
    rw [eqKernelRust_eq, eqKernel_length, List.length_nil] at this
    exact absurd this (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
  · simp [kFirst, hs]
  · simp [kFirst, kWeights, keccakBits]

/-! ## A claim in memory -/

theorem ClaimOut.claimAt {s u : MachineState} {a : Word} {c : KeccakClaim} (h : ClaimOut s u a c) :
    claimAt u a = c := by
  obtain ⟨v, mu, pt, w⟩ := c
  simp only [Gkr.claimAt, h.mu.elems, h.point.elems, h.weights.elems, h.value]

theorem ClaimOut.mono {s s' u : MachineState} {a : Word} {c : KeccakClaim} (h : ClaimOut s' u a c)
    (hs : heapNext s ≤ heapNext s') : ClaimOut s u a c :=
  ⟨Open.newVecE_mono h.mu hs, Open.newVecE_mono h.point hs, Open.newVecE_mono h.weights hs, h.value⟩

/-- A claim in a slot that a step does not write. -/
theorem ClaimOut.step {s u v : MachineState} (hpre : VerifyKeccakPre s) (B : Base s u)
    (hH : HeapOk v) (hN : heapNext u ≤ heapNext v) {rs : List (Nat × Nat)} {sp : Bool}
    (hok : SlotsOk rs = true) {J : Nat} (hJ : J ≤ 5248) (h96 : 96 ≤ J)
    (hsep : SlotsSep rs J 96 = true) (F : DFrame u v (SW s u v rs sp)) {cl : KeccakClaim}
    (h : ClaimOut s u (s.getReg .x2 - BitVec.ofNat 64 J) cl) :
    ClaimOut s v (s.getReg .x2 - BitVec.ofNat 64 J) cl := by
  have hb := bounds hpre
  have e24 : s.getReg .x2 - BitVec.ofNat 64 J + 24 = s.getReg .x2 - BitVec.ofNat 64 (J - 24) :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb, hJ, h96])
  have e48 : s.getReg .x2 - BitVec.ofNat 64 J + 48 = s.getReg .x2 - BitVec.ofNat 64 (J - 48) :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb, hJ, h96])
  have e72 : s.getReg .x2 - BitVec.ofNat 64 J + 72 = s.getReg .x2 - BitVec.ofNat 64 (J - 72) :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb, hJ, h96])
  have hp := h.point
  have hw := h.weights
  have hv := h.value
  rw [e24] at hp
  rw [e48] at hw
  rw [e72] at hv
  refine ⟨SW.vec hpre B hH hN hok hJ (by omega) (SlotsSep.sub hsep (le_refl _) (by omega)) F h.mu,
    ?_, ?_, ?_⟩
  · rw [e24]
    exact SW.vec hpre B hH hN hok (by omega) (by omega) (SlotsSep.sub hsep (by omega) (by omega)) F hp
  · rw [e48]
    exact SW.vec hpre B hH hN hok (by omega) (by omega) (SlotsSep.sub hsep (by omega) (by omega)) F hw
  · rw [e72, SW.e hpre hH hok (by omega) (by omega) (SlotsSep.sub hsep (by omega) (by omega)) F]
    exact hv

/-- A claim copied doubleword by doubleword. -/
theorem claimOut_copy {s v : MachineState} {a b : Word} {cl : KeccakClaim} (h : ClaimOut s v a cl)
    (ha : a.toNat + 96 ≤ 2 ^ 64) (hb : b.toNat + 96 ≤ 2 ^ 64)
    (e : ∀ j < 12, ∀ x y : Word, x.toNat = b.toNat + 8 * j → y.toNat = a.toNat + 8 * j →
      v.getMem x = v.getMem y) : ClaimOut s v b cl := by
  have q (j : Nat) (hj : j < 12) (o k : Nat) (hk : o + k = 8 * j) (x y : Word)
      (hx : x.toNat = b.toNat + o + k) (hy : y.toNat = a.toNat + o + k) : v.getMem x = v.getMem y :=
    e j hj x y (by omega) (by omega)
  have cp (o j : Nat) (hj : j + 2 < 12) (ho : o = 8 * j) (xs : List E)
      (hv : NewVecE s v (a + BitVec.ofNat 64 o) xs) : NewVecE s v (b + BitVec.ofNat 64 o) xs :=
    newVecE_copy hv (q j (by omega) o 0 (by omega) _ _ (by addr_omega [hb, ho, hj]) (by addr_omega [ha, ho, hj]))
      (q (j + 1) (by omega) o 8 (by omega) _ _ (by addr_omega [hb, ho, hj]) (by addr_omega [ha, ho, hj]))
      (q (j + 2) (by omega) o 16 (by omega) _ _ (by addr_omega [hb, ho, hj]) (by addr_omega [ha, ho, hj]))
  have z (x : Word) : x + BitVec.ofNat 64 0 = x := BitVec.add_zero x
  have hm := h.mu
  rw [← z a] at hm
  refine ⟨by rw [← z b]; exact cp 0 0 (by decide) rfl _ hm, cp 24 3 (by decide) rfl _ h.point,
    cp 48 6 (by decide) rfl _ h.weights, ?_⟩
  rw [← h.value]
  unfold Rv64Verifier.eAt
  rw [q 9 (by decide) 72 0 rfl (b + 72) (a + 72) (by addr_omega [hb]) (by addr_omega [ha]),
    q 10 (by decide) 72 8 rfl (b + 72 + 8) (a + 72 + 8) (by addr_omega [hb]) (by addr_omega [ha]),
    q 11 (by decide) 72 16 rfl (b + 72 + 16) (a + 72 + 16) (by addr_omega [hb]) (by addr_omega [ha])]

/-- A non-empty `Vec` allocated since the entry. -/
theorem vec_facts {s u : MachineState} (hpre : VerifyKeccakPre s) (B : Base s u) {a : Word}
    {xs : List E} (h : NewVecE s u a xs) (hne : xs ≠ []) :
    VecRegion u a ∧ VecOutside u a ∧ (∀ lo m, heapEnd ≤ lo.toNat → VecApart u a lo m) ∧
      VecApart u a (s.getReg .x11 + 8) 344 := by
  rcases vec_heaped hpre B h with h0 | H
  · exfalso
    apply hne
    rw [← h.elems, vecEs, h0]
    rfl
  · exact ⟨Or.inr H.region, H.outside, fun lo m hl ↦ H.above lo m hl, H.self⟩

/-! ## What the rest of the body reads from the frame -/

/-- The spills, the first claim at `f + 200`, the committed outputs' value at `f + 176`. -/
structure K (s u : MachineState) (first : KeccakClaim) (c : E) : Prop where
  base : Base s u
  ok : OK s
  m32 : u.getMem (s.getReg .x2 - 5216) = s.getReg .x12 - 4
  m48 : u.getMem (s.getReg .x2 - 5200) = s.getReg .x10
  m56 : u.getMem (s.getReg .x2 - 5192) = s.getReg .x14
  m64 : u.getMem (s.getReg .x2 - 5184) = 2
  firstV : ClaimOut s u (s.getReg .x2 - 5048) first
  firstLens : Lens first
  committed : eAt u (s.getReg .x2 - 5072) = c

theorem K.step {s u v : MachineState} {first : KeccakClaim} {c : E} (hpre : VerifyKeccakPre s)
    (k : K s u first c) (hx2 : v.getReg .x2 = s.getReg .x2 - 5248) (hH : HeapOk v)
    (hN : heapNext u ≤ heapNext v) {rs : List (Nat × Nat)} {sp : Bool} (hok : SlotsOk rs = true)
    (h1 : SlotsSep rs 5216 8 = true) (h2 : SlotsSep rs 5200 24 = true)
    (h3 : SlotsSep rs 5072 120 = true) (F : DFrame u v (SW s u v rs sp)) : K s v first c :=
  { base := k.base.step hpre hx2 hH hN hok F
    ok := k.ok
    m32 := (SW.mem hpre hH hok (J := 5216) (by decide) (by decide) h1 F).trans k.m32
    m48 := (SW.mem hpre hH hok (J := 5200) (by decide) (by decide)
      (SlotsSep.sub h2 (le_refl _) (by omega)) F).trans k.m48
    m56 := (SW.mem hpre hH hok (J := 5192) (by decide) (by decide)
      (SlotsSep.sub h2 (by omega) (by omega)) F).trans k.m56
    m64 := (SW.mem hpre hH hok (J := 5184) (by decide) (by decide)
      (SlotsSep.sub h2 (by omega) (by omega)) F).trans k.m64
    firstV := ClaimOut.step hpre k.base hH hN hok (J := 5048) (by decide) (by decide)
      (SlotsSep.sub h3 (by omega) (by omega)) F k.firstV
    firstLens := k.firstLens
    committed := (SW.e hpre hH hok (J := 5072) (by decide) (by decide)
      (SlotsSep.sub h3 (le_refl _) (by omega)) F).trans k.committed }

theorem K.same {s u v : MachineState} {first : KeccakClaim} {c : E} (hpre : VerifyKeccakPre s)
    (k : K s u first c) (hx2 : v.getReg .x2 = s.getReg .x2 - 5248) (hm : ∀ a, v.getMem a = u.getMem a) :
    K s v first c := by
  have hN : heapNext v = heapNext u := by simp only [heapNext, hm]
  exact k.step hpre hx2 ⟨by rw [hN]; exact k.base.heap.lo, by rw [hN]; exact k.base.heap.hi⟩
    (le_of_eq hN.symm) (rs := []) (sp := false) (by decide) (by decide) (by decide) (by decide)
    (DFrame.of_same hm _)

/-! ## `verify_layer`'s precondition -/

theorem layer_pre {s u : MachineState} (hpre : VerifyKeccakPre s) (B : Base s u) {J : Nat}
    (hJ1 : 3392 ≤ J) (hJ2 : J ≤ 5048) (hJ8 : J % 8 = 0) {cl : KeccakClaim}
    (hc : ClaimOut s u (s.getReg .x2 - BitVec.ofNat 64 J) cl) (hl : Lens cl)
    (hx10 : u.getReg .x10 = s.getReg .x2 - 3296) (hx11 : u.getReg .x11 = s.getReg .x11)
    (hx13 : u.getReg .x13 = 12) (hx14 : (u.getReg .x14).toNat < 12)
    (hx15 : u.getReg .x15 = s.getReg .x2 - BitVec.ofNat 64 J) : VerifyLayerPre u := by
  have hb := bounds hpre
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hS := hpre.self.self
  have hss := hpre.selfStack
  have tp : TPre 96 verifyLayerStack u := B.tpre hpre 3296 hx10 hx11 (by decide) (by decide)
    (by decide) (by unfold verifyLayerStack openStack; omega) (by decide)
  obtain ⟨m1, m2, m3, m4⟩ := vec_facts hpre B hc.mu hl.1
  obtain ⟨p1, p2, p3, p4⟩ := vec_facts hpre B hc.point hl.2.1
  obtain ⟨w1, w2, w3, w4⟩ := vec_facts hpre B hc.weights hl.2.2
  unfold verifyKeccakStack at hb hsm hab hnx hss
  have st : heapEnd ≤ (stackLo u verifyLayerStack).toNat := by
    simp only [stackLo, B.x2]; unfold verifyLayerStack; addr_omega [hb, hab]
  have ot : heapEnd ≤ (u.getReg .x10).toNat := by rw [hx10]; addr_omega [hb, hab]
  have hal : (s.getReg .x11 + 360).toNat % 8 = 0 := by addr_omega [hS]
  have hck : Checked u (u.getReg .x11) := by
    rw [hx11]
    have h := hpre.checked
    simp only [Checked] at h ⊢
    rw [byteAt_eq, alignDown_of_within hal (le_refl _) (by omega), B.byte hpre]
    rwa [byteAt_eq, alignDown_of_within hal (le_refl _) (by omega)] at h
  have e : lClaim u = s.getReg .x2 - BitVec.ofNat 64 J := hx15
  exact { tp with
    depth := hx13
    step := hx14
    checked := hck
    claim := by rw [e]; addr_omega [hb, hsm, hJ1, hJ2, hJ8]
    mu := by rw [e]; exact m1
    point := by rw [e]; exact p1
    weights := by rw [e]; exact w1
    claimFree := by rw [e]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx, hJ1, hJ2]
    muFree := by rw [e]; exact m2
    pointFree := by rw [e]; exact p2
    weightsFree := by rw [e]; exact w2
    claimStack := by
      rw [e]; simp only [stackLo, B.x2]; unfold verifyLayerStack; addr_omega [hb, hJ1, hJ2]
    muStack := by rw [e]; exact m3 _ _ st
    pointStack := by rw [e]; exact p3 _ _ st
    weightsStack := by rw [e]; exact w3 _ _ st
    claimOut := by rw [e, hx10]; addr_omega [hb, hJ1, hJ2]
    muOut := by rw [e]; exact m3 _ _ ot
    pointOut := by rw [e]; exact p3 _ _ ot
    weightsOut := by rw [e]; exact w3 _ _ ot
    claimSelf := by rw [e, hx11]; addr_omega [hb, hss, hS, hJ1, hJ2]
    muSelf := by rw [e, hx11]; exact m4
    pointSelf := by rw [e, hx11]; exact p4
    weightsSelf := by rw [e, hx11]; exact w4 }

/-! ## The call -/

/-- A call to `verify_layer` with the claim at `f + 5248 - J` and its result at `f + 1952`: back
with `Err` and the mirror failing, or with the mirror's next claim. -/
theorem layer_call (hVL : VerifyLayerSpec) {s u : MachineState} {first : KeccakClaim} {c : E}
    {J k : Nat} {cl : KeccakClaim} {f : KeccakClaim → TM KeccakOpenings}
    (hpre : VerifyKeccakPre s) (Kk : K s u first c) (hpc : u.pc = 0x8000f04c)
    (hJ1 : 3392 ≤ J) (hJ2 : J ≤ 5048) (hJ8 : J % 8 = 0)
    (hc : ClaimOut s u (s.getReg .x2 - BitVec.ofNat 64 J) cl) (hl : Lens cl)
    (hx10 : u.getReg .x10 = s.getReg .x2 - 3296) (hx11 : u.getReg .x11 = s.getReg .x11)
    (hx12 : u.getReg .x12 = s.getReg .x12) (hx13 : u.getReg .x13 = 12)
    (hx14 : u.getReg .x14 = BitVec.ofNat 64 k) (hk : k < 12)
    (hx15 : u.getReg .x15 = s.getReg .x2 - BitVec.ofNat 64 J)
    (hR : Rest s u (verifyLayerRust ⟨(s.getReg .x12).toNat, 12⟩ k cl >>= f)) :
    ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨ (t.pc = returnAddress u ∧ Preserves u t ∧
      K s t first c ∧ DFrame u t (SW s u t [(3296, 96)] true) ∧
      ((t.getMem (s.getReg .x2 - 3296) = errNiche ∧ Fails s) ∨
        (t.getMem (s.getReg .x2 - 3296) ≠ errNiche ∧ ∃ c', ClaimOut s t (s.getReg .x2 - 3296) c' ∧
          Lens c' ∧ Rest s t (f c'))))) := by
  have B := Kk.base
  have hk' : (u.getReg .x14).toNat < 12 := by rw [hx14, BitVec.toNat_ofNat]; omega
  have hvp := layer_pre hpre B hJ1 hJ2 hJ8 hc hl hx10 hx11 hx13 hk' hx15
  obtain ⟨t, hr, ⟨hpc', hpres, hpost⟩ | hd⟩ := hVL u hpc hvp
  swap
  · exact ⟨t, hr, Or.inl hd⟩
  have x2t : t.getReg .x2 = s.getReg .x2 - 5248 := (hpres.reg .x2).trans B.x2
  have F : DFrame u t (SW s u t [(3296, 96)] true) := DFrame.mono hpost.frame fun a ha ↦
    tframe_sw hpre 3296 B.x2 hx10 hx11 (by unfold verifyLayerStack openStack; omega) a ha
  have Kt := Kk.step hpre x2t hpost.heap hpost.mono (by decide) (by decide) (by decide) (by decide) F
  have hcl : claimAt u (lClaim u) = cl := by
    rw [show lClaim u = s.getReg .x2 - BitVec.ofNat 64 J from hx15]; exact ClaimOut.claimAt hc
  have hsh : shapeOf u = ⟨(s.getReg .x12).toNat, 12⟩ := by rw [Open.shapeOf_eq hx13, hx12]
  have hkk : (u.getReg .x14).toNat = k := by rw [hx14, BitVec.toNat_ofNat]; omega
  have hv (T : TState) (hT : TranscriptAt u (s.getReg .x11) T) :
      match (verifyLayerRust ⟨(s.getReg .x12).toNat, 12⟩ k cl).run T with
      | some (c', T') => vecCap t (s.getReg .x2 - 3296) ≠ errNiche ∧
          ClaimOut u t (s.getReg .x2 - 3296) c' ∧ TranscriptAt t (s.getReg .x11) T'
      | none => vecCap t (s.getReg .x2 - 3296) = errNiche := by
    have h := hpost.value T (by rw [hx11]; exact hT)
    rw [hsh, hkk, hcl, hx10, hx11] at h
    exact h
  refine ⟨t, hr, Or.inr ⟨hpc', hpres, Kt, F, ?_⟩⟩
  by_cases hcap : t.getMem (s.getReg .x2 - 3296) = errNiche
  · refine Or.inl ⟨hcap, hR.fail fun T hT ↦ ?_⟩
    have h := hv T hT
    generalize (verifyLayerRust ⟨(s.getReg .x12).toNat, 12⟩ k cl).run T = o at h ⊢
    rcases o with _ | ⟨c', T'⟩
    · rfl
    · exact absurd hcap h.1
  · refine Or.inr ⟨hcap, ?_⟩
    obtain ⟨T₀, hT₀⟩ := Open.exists_T u (s.getReg .x11)
    have h₀ := hv T₀ hT₀
    generalize ho : (verifyLayerRust ⟨(s.getReg .x12).toNat, 12⟩ k cl).run T₀ = o at h₀
    rcases o with _ | ⟨c₀, T₀'⟩
    · exact absurd h₀ hcap
    obtain ⟨-, hco, -⟩ := h₀
    refine ⟨c₀, ClaimOut.mono hco B.mono, lens_layer hl.2.1 ho, hR.step fun T hT ↦ ?_⟩
    have h := hv T hT
    generalize (verifyLayerRust ⟨(s.getReg .x12).toNat, 12⟩ k cl).run T = o at h
    rcases o with _ | ⟨c₁, T₁⟩
    · exact absurd h hcap
    obtain ⟨-, hc₁, hT₁⟩ := h
    have e : c₁ = c₀ := (ClaimOut.claimAt hc₁).symm.trans (ClaimOut.claimAt hco)
    subst e
    exact ⟨T₁, rfl, hT₁⟩

/-- `memcpy(f + 320, f + 1976, 72)`. -/
theorem memcpy_72 (hMC : Runtime.MemcpySpec 0x800126e4) {s w : MachineState}
    (hpre : VerifyKeccakPre s) (B : Base s w) (hpc : w.pc = 0x800126e4)
    (hx10 : w.getReg .x10 = s.getReg .x2 - 4928) (hx11 : w.getReg .x11 = s.getReg .x2 - 3272)
    (hx12 : w.getReg .x12 = 72) :
    ∃ w', Reaches Image.code w w' ∧ (Dead Image.code w' ∨ (w'.pc = returnAddress w ∧
      Preserves w w' ∧ DFrame w w' (SW s w w' [(4928, 72)] false) ∧ heapNext w' = heapNext w ∧
      ∀ j < 9, w'.getMem (s.getReg .x2 - 4928 + BitVec.ofNat 64 (8 * j)) =
        w.getMem (s.getReg .x2 - 3272 + BitVec.ofNat 64 (8 * j)))) := by
  have hb := bounds hpre
  have hsm := hpre.stack.mapped (by decide) (by decide)
  unfold verifyKeccakStack at hb hsm
  have h72 : (w.getReg .x12).toNat = 72 := by rw [hx12]; rfl
  have hmc : Runtime.MemcpyPre w := {
    dst := by rw [hx10, h72]; addr_omega [hb, hsm]
    src := by rw [hx11, h72]; addr_omega [hb, hsm]
    apart := by rw [hx10, hx11, h72]; addr_omega [hb]
    stack := (hpre.stack.sub 5248 B.x2 (by unfold verifyKeccakStack; decide) (by decide)
      (by decide) (by decide) (by decide)).toStackOk
    dstStack := by rw [hx10, h72]; simp only [stackLo, B.x2]; addr_omega [hb]
    srcStack := by rw [hx11, h72]; simp only [stackLo, B.x2]; addr_omega [hb] }
  obtain ⟨w', hr, ⟨hpc', hpres, hpost⟩ | hd⟩ := hMC w hpc hmc
  swap
  · exact ⟨w', hr, Or.inl hd⟩
  have bytes := hpost.bytes
  rw [hx10, hx11, h72] at bytes
  have hnx := hpre.stack.next
  unfold verifyKeccakStack at hnx
  have hN0 : w'.getMem nextAddr = w.getMem nextAddr :=
    DFrame.of_byteFrame hpost.frame _ fun i hi h ↦ by
      rw [hx10, h72] at h
      simp only [stackLo, B.x2] at h
      rcases h with h | h <;> addr_omega [h, hi, hb, hnx]
  have hN : heapNext w' = heapNext w := by simp only [heapNext, hN0]
  refine ⟨w', hr, Or.inr ⟨hpc', hpres, (DFrame.of_byteFrame hpost.frame).mono fun a ha ↦ ?_, hN,
    fun j hj ↦ getMem_eq_of_bytesAt bytes (by addr_omega [hb]) (by addr_omega [hb]) (by omega)
      (by omega)⟩⟩
  rw [hx10, h72] at ha
  rcases ha with h | h
  · exact Or.inl ⟨(4928, 72), List.mem_singleton_self _, h⟩
  · exact Or.inr (Or.inl (stk_sw hpre B.x2 (k := memcpyStack) (by decide) h))

/-- The result's header stored to `f + 296`, the rest copied to `f + 320`: the claim at
`f + 296`. -/
theorem stored {s v : MachineState} {cl : KeccakClaim} (hpre : VerifyKeccakPre s)
    (hc : ClaimOut s v (s.getReg .x2 - 3296) cl)
    (h0 : v.getMem (s.getReg .x2 - 4952) = v.getMem (s.getReg .x2 - 3296))
    (h8 : v.getMem (s.getReg .x2 - 4944) = v.getMem (s.getReg .x2 - 3288))
    (h16 : v.getMem (s.getReg .x2 - 4936) = v.getMem (s.getReg .x2 - 3280))
    (hcopy : ∀ j < 9, v.getMem (s.getReg .x2 - 4928 + BitVec.ofNat 64 (8 * j)) =
      v.getMem (s.getReg .x2 - 3272 + BitVec.ofNat 64 (8 * j))) :
    ClaimOut s v (s.getReg .x2 - 4952) cl := by
  have hb := bounds hpre
  unfold verifyKeccakStack at hb
  refine claimOut_copy hc (by addr_omega [hb]) (by addr_omega [hb]) fun j hj x y hx hy ↦ ?_
  by_cases h3 : j < 3
  · rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · rw [BitVec.eq_of_toNat_eq (x := x) (y := s.getReg .x2 - 4952) (by addr_omega [hx, hb]),
        BitVec.eq_of_toNat_eq (x := y) (y := s.getReg .x2 - 3296) (by addr_omega [hy, hb])]
      exact h0
    · rw [BitVec.eq_of_toNat_eq (x := x) (y := s.getReg .x2 - 4944) (by addr_omega [hx, hb]),
        BitVec.eq_of_toNat_eq (x := y) (y := s.getReg .x2 - 3288) (by addr_omega [hy, hb])]
      exact h8
    · rw [BitVec.eq_of_toNat_eq (x := x) (y := s.getReg .x2 - 4936) (by addr_omega [hx, hb]),
        BitVec.eq_of_toNat_eq (x := y) (y := s.getReg .x2 - 3280) (by addr_omega [hy, hb])]
      exact h16
  · have hj' : j - 3 < 9 := by omega
    rw [BitVec.eq_of_toNat_eq (x := x) (y := s.getReg .x2 - 4928 + BitVec.ofNat 64 (8 * (j - 3)))
        (by addr_omega [hx, hb, hj, h3]),
      BitVec.eq_of_toNat_eq (x := y) (y := s.getReg .x2 - 3272 + BitVec.ofNat 64 (8 * (j - 3)))
        (by addr_omega [hy, hb, hj, h3])]
    exact hcopy _ hj'

end Rv64Verifier.Gkr.Keccak
