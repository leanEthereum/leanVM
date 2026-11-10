import Rv64Verifier.Proofs.Bus.VbbTail14

/-!
# `verify_bus_balance` past the GKR loop: `memory[0..3]`'s claims

From `alloc`'s entry (`Points`): the claims' buffer (168 bytes; a null pointer traps), the three
claims of `memory` written to it and its `Vec` at `S - 840`, then `copy4`, to `0x80006f88`
(`Cl3`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The `i`-th claim of a buffer at `P`, from a `Vec` in registers and its fields' words. -/
theorem NewVecR.claimAt' {s t : MachineState} {P cap ptr len : Word} {i : Nat} {xs : List E}
    (h : NewVecR s t cap ptr len xs) (hlo : heapStart ≤ heapNext s) (hl : PtrLo t ptr len)
    (e0 : t.getMem (P + BitVec.ofNat 64 (56 * i)) = cap)
    (e8 : t.getMem (P + BitVec.ofNat 64 (56 * i + 8)) = ptr)
    (e16 : t.getMem (P + BitVec.ofNat 64 (56 * i + 16)) = len) {col : Nat}
    (ec : (t.getMem (P + BitVec.ofNat 64 (56 * i + 24))).toNat = col) {x : E}
    (ex : eAt t (P + BitVec.ofNat 64 (56 * i + 32)) = x) :
    ClaimAt s t (P + BitVec.ofNat 64 (56 * i)) ⟨col, xs, x⟩ := by
  have a (j : Nat) : P + BitVec.ofNat 64 (56 * i) + BitVec.ofNat 64 j =
      P + BitVec.ofNat 64 (56 * i + j) := by rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h.claimAt hlo hl e0 ((a 8).symm ▸ e8) ((a 16).symm ▸ e16) ((a 24).symm ▸ ec)
    ((a 32).symm ▸ ex)

/-- An `E` from its three words at `P + j`. -/
theorem eAt_off {t u : MachineState} {P b : Word} {j : Nat}
    (h0 : t.getMem (P + BitVec.ofNat 64 j) = u.getMem b)
    (h8 : t.getMem (P + BitVec.ofNat 64 (j + 8)) = u.getMem (b + 8))
    (h16 : t.getMem (P + BitVec.ofNat 64 (j + 16)) = u.getMem (b + 16)) :
    eAt t (P + BitVec.ofNat 64 j) = eAt u b := by
  refine eAt_congr h0 ?_ ?_
  · rw [show P + BitVec.ofNat 64 j + 8 = P + BitVec.ofNat 64 (j + 8) by
      rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl]
    exact h8
  · rw [show P + BitVec.ofNat 64 j + 16 = P + BitVec.ofNat 64 (j + 16) by
      rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl]
    exact h16

/-- The claims of `memory[0..3]`, as the mirror lists them. -/
def memClaims (s : MachineState) (state : GkrState) (mem : List E) : List ColumnClaim :=
  [memory0, memory1, memory2].map fun column ↦
    ⟨column, state.point.take (logMem s).toNat, mem.getD column 0⟩

/-- At `0x80006f88`, the claims of `memory` written, `point[..log_memory]` copied again into
`s1`, `s3`; the result's address in `s5`, `log_bytecode` in `s7`, `log_memory` in `s8`, the point's
buffer in `s11`. -/
structure Cl3 (bev : MachineState → Word → List E → Option E) (s w : MachineState) (k : Start)
    (state : GkrState) (mem : List E) (mf bf : E) : Prop where
  inv : Inv s w
  kept : Kept s w k
  claims : ClaimsOk s w (w.getMem (s.getReg .x2 - 840)) (w.getMem (s.getReg .x2 - 832))
    (w.getMem (s.getReg .x2 - 824)) (memClaims s state mem)
  len : w.getMem (s.getReg .x2 - 824) = 3
  c3 : NewVecR s w (w.getReg .x9) (w.getReg .x19) (logMem s) (state.point.take (logMem s).toNat)
  c3Lo : PtrLo w (w.getReg .x19) (logMem s)
  x20 : w.getReg .x20 = s.getReg .x12
  x21 : w.getReg .x21 = s.getReg .x10
  x23 : w.getReg .x23 = logBc s
  x24 : w.getReg .x24 = logMem s
  x27 : w.getReg .x27 = w.getMem (s.getReg .x2 - 1256)
  memory : NewVecE s w (s.getReg .x2 - 864) mem
  values : NewVecE s w (s.getReg .x2 - 176) state.values
  point : NewVecR s w (w.getMem (s.getReg .x2 - 1320)) (w.getMem (s.getReg .x2 - 1256))
    (w.getMem (s.getReg .x2 - 1144)) state.point
  valuesPtr : w.getMem (s.getReg .x2 - 1280) = vecPtr w (s.getReg .x2 - 176)
  pushPtr : w.getMem (s.getReg .x2 - 1272) = vecPtr s (s.getReg .x11 + 24)
  lm : (logMem s).toNat ≤ state.point.length
  lb : (logBc s).toNat ≤ state.point.length
  mfEq : mf = eOf3 (w.getReg .x25) (w.getReg .x22) (w.getMem (s.getReg .x2 - 1112))
  bfEq : bf = eOf3 (w.getReg .x26) (w.getMem (s.getReg .x2 - 1120))
    (w.getMem (s.getReg .x2 - 1128))
  tracks : Tracks (prog bev s) (s.getReg .x12) s w (rest bev s k state mem mf bf)
  pointLo : PtrLo w (w.getMem (s.getReg .x2 - 1256)) (w.getMem (s.getReg .x2 - 1144))

theorem claims3 (hA : AllocSpec) (hT : TryAllocZeroedSpec) (hM : MemcpySpec 0x800126e4)
    {bev : MachineState → Word → List E → Option E} {s y : MachineState} {k : Start}
    {state : GkrState} {mem : List E} {mf bf : E} (hpre : BusBalancePre s)
    (P : Points bev s y k state mem mf bf) (hpc : y.pc = 0x80000284) :
    ∃ w, Reaches Image.code y w ∧ (Dead Image.code w ∨
      (w.pc = 0x80006f88 ∧ Cl3 bev s w k state mem mf bf)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  obtain ⟨v, hrv, ⟨hpcv, hp, post⟩ | hd⟩ := allocCall hA P.inv (Reaches.refl y) hpc P.x10
  swap
  · exact ⟨v, hrv, Or.inl hd⟩
  have hpc' : v.pc = 0x80006e9c := by rw [hpcv, returnAddress_eq, P.x1]; decide
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80006e9c_spec hpc' trivial
  have k₁ := b80006e9c_keeps h₁
  have m₁ := b80006e9c_mem_same h₁
  by_cases hz : v.getReg .x10 = 0
  · exact ⟨u₁, hrv.trans hr₁, Or.inl (dead_of_fetch (by
      rw [b80006e9c_pc_taken h₁ hz]; exact Option.isNone_iff_eq_none.mp (by decide +kernel)))⟩
  have pc₁ := b80006e9c_pc_not_taken h₁ hz
  have al : (v.getReg .x10).toNat % 8 = 0 := by have := post.aligned; rw [P.x10] at this; exact this
  have ab := post.above
  have nx : heapNext v = (v.getReg .x10).toNat + 168 := by
    have := post.next; rw [P.x11] at this; exact this
  have hhv := post.heap.hi
  have hly := P.inv.heap.lo
  have hmo := P.inv.mono
  have hx := hpre.stack.next
  rw [stackLo_eq] at hx
  have x10₁ : u₁.getReg .x10 = v.getReg .x10 := k₁ .x10 (by decide)
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 1344 := by
    rw [k₁ .x2 (by decide), hp .x2 (by decide), P.inv.sp]
  simp only [heapNext, heapEnd, heapStart] at nx hhv hly ab hmo
  have hlo : 536870912 ≤ (v.getReg .x10).toNat := by omega
  have hhi : (v.getReg .x10).toNat + 168 ≤ 2013265920 := by omega
  have hheap : ValidMemRange (v.getReg .x10) 21 :=
    heapRange al (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80006ea0_spec pc₁ (by
    rv_eval [sp₁, x10₁]
    and_intros <;> first
      | valid_access hval [hb1]
      | valid_access hheap [hlo, hhi, al]
      | addr_omega [hb1, hlo, hhi])
  have k₂ := b80006ea0_keeps h₂
  have fr : DFrame u₁ u₂ fun a ↦ Within a (s.getReg .x2 - 840) 24 ∨
      Within a (v.getReg .x10) 168 := fun a ha ↦
    h₂.frame a (by
      rv_eval [sp₁, x10₁]
      and_intros <;> intro he <;> exact ha 0 (by decide) (by
        rw [add_ofNat_zero, he]; addr_omega [hb1, hlo, hhi]))
  have hnz : u₂.getMem nextAddr = v.getMem nextAddr := by
    rw [fr nextAddr fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hi, hx, hb1, hlo, hhi], m₁]
  have hn₂ : heapNext u₂ = heapNext v := by simp only [heapNext, hnz]
  have F : DFrame y u₂ fun a ↦ Within a (s.getReg .x2 - 840) 24 ∨
      Within a (s.getReg .x2 - 4544) 3200 ∨ Within a nextAddr 8 ∨ Fresh y u₂ a := fun a ha ↦ by
    rw [fr a (fun i hi hw ↦ ha i hi (by
        rcases hw with hw | hw
        · exact Or.inl hw
        · refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩)) <;> simp only [heapNext, hnz] <;>
            addr_omega [hw, ab, nx, hhi])), m₁,
      post.mem a (fun he ↦ ha 0 (by decide) (by
        rw [add_ofNat_zero, he]; exact Or.inr (Or.inr (Or.inl (by addr_omega [])))))]
  have st₂ : StepS s y u₂ (Within · (s.getReg .x2 - 840) 24) :=
    ⟨F, ⟨by rw [hn₂]; exact post.heap.lo, by rw [hn₂]; exact post.heap.hi⟩,
      by simp only [heapNext, hnz]; omega,
      by rw [k₂ .x2 (by decide), k₁ .x2 (by decide), hp .x2 (by decide)]⟩
  have f840 : FrameW s (Within · (s.getReg .x2 - 840) 24) := fun a ha ↦ by addr_omega [ha, hb1]
  have I₂ := P.inv.afterR hpre f840 st₂.toR
  have sp₂ : u₂.getReg .x2 = s.getReg .x2 - 1344 := I₂.sp
  have ry (r : Reg) (hr : r ∈ ([.x8, .x18, .x19, .x20, .x21, .x22, .x23, .x25, .x26, .x27] :
      List Reg)) : u₂.getReg r = y.getReg r := by
    rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _),
      hp r (by unfold calleeSaved; exact mem_of_mem hr _)]
  have ym (a : Word) (hn : a ≠ nextAddr) : u₁.getMem a = y.getMem a := by
    rw [m₁, post.mem a hn]
  have ld (j k : Nat) (hjk : j + k = 1344) (hk1 : 104 < k) (hk2 : k ≤ 1344) :
      u₁.getMem (s.getReg .x2 - 1344 + BitVec.ofNat 64 j) =
        y.getMem (s.getReg .x2 - BitVec.ofNat 64 k) := by
    rw [ym _ (fun he ↦ by
      have := congrArg BitVec.toNat he; revert this; addr_omega [hb1, hjk, hk1, hk2])]
    exact congrArg y.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hjk, hk2])
  have lm₁ : u₁.getMem (s.getReg .x2 - 1344 + 208) = logMem s :=
    (ld 208 1136 rfl (by omega) (by omega)).trans P.kept.lm
  -- the three claims
  have hc {cap ptr : Word} (c : NewVecR s y cap ptr (logMem s) (state.point.take (logMem s).toNat)) :
      NewVecR s u₂ cap ptr (logMem s) (state.point.take (logMem s).toNat) :=
    c.keepR hpre st₂.toR f840
  have hlo' : heapStart ≤ heapNext s := hpre.heap.lo
  have pv := post.heap.lo
  have mx (j : Nat) : u₂.getMem (v.getReg .x10 + BitVec.ofNat 64 j) =
      u₂.getMem (u₁.getReg .x10 + BitVec.ofNat 64 j) := by rw [x10₁]
  have ap {cap ptr len : Word} {xs : List E} (c : NewVecR s y cap ptr len xs) (i : Nat)
      (e0 : u₂.getMem (v.getReg .x10 + BitVec.ofNat 64 (56 * i)) = cap)
      (e8 : u₂.getMem (v.getReg .x10 + BitVec.ofNat 64 (56 * i + 8)) = ptr) :
      Apart (vecPtr u₂ (v.getReg .x10 + BitVec.ofNat 64 (56 * i)))
        ((vecCap u₂ (v.getReg .x10 + BitVec.ofNat 64 (56 * i))).toNat * 24) (v.getReg .x10)
        (56 * (3 : Word).toNat) := by
    simp only [vecPtr, vecCap]
    rw [e0, show v.getReg .x10 + BitVec.ofNat 64 (56 * i) + 8 =
      v.getReg .x10 + BitVec.ofNat 64 (56 * i + 8) by rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl,
      e8]
    have hb := c.buf
    simp only [NewBuf, heapNext] at hb
    simp only [Apart]
    rcases hb.2 with h0 | ⟨b1, b2⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inr (Or.inl (by omega)))
  have ld3 (j k : Nat) (hjk : j + k = 1344) (hk1 : 104 < k) (hk2 : k ≤ 1344) (hk3 : 120 < k) :
      u₁.getMem (s.getReg .x2 - 1344 + BitVec.ofNat 64 j) =
        y.getMem (s.getReg .x2 - BitVec.ofNat 64 k) ∧
      u₁.getMem (s.getReg .x2 - 1344 + BitVec.ofNat 64 (j + 8)) =
        y.getMem (s.getReg .x2 - BitVec.ofNat 64 k + 8) ∧
      u₁.getMem (s.getReg .x2 - 1344 + BitVec.ofNat 64 (j + 16)) =
        y.getMem (s.getReg .x2 - BitVec.ofNat 64 k + 16) :=
    ⟨ld j k hjk hk1 hk2, (ld (j + 8) (k - 8) (by omega) (by omega) (by omega)).trans
      (congrArg y.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hk2, hk3])),
      (ld (j + 16) (k - 16) (by omega) (by omega) (by omega)).trans
      (congrArg y.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hk2, hk3]))⟩
  have m736 := ld3 736 608 rfl (by omega) (by omega) (by omega)
  have m1096 := ld3 1096 248 rfl (by omega) (by omega) (by omega)
  have m1192 := ld3 1192 152 rfl (by omega) (by omega) (by omega)
  rw [← sp₁] at m736 m1096 m1192 lm₁
  have r8 : u₁.getReg .x8 = y.getReg .x8 := by rw [k₁ .x8 (by decide), hp .x8 (by decide)]
  have r21 : u₁.getReg .x21 = y.getReg .x21 := by rw [k₁ .x21 (by decide), hp .x21 (by decide)]
  have r19 : u₁.getReg .x19 = y.getReg .x19 := by rw [k₁ .x19 (by decide), hp .x19 (by decide)]
  have r23 : u₁.getReg .x23 = y.getReg .x23 := by rw [k₁ .x23 (by decide), hp .x23 (by decide)]
  have r27 : u₁.getReg .x27 = y.getReg .x27 := by rw [k₁ .x27 (by decide), hp .x27 (by decide)]
  have r24 : u₁.getReg .x24 = y.getReg .x24 := by rw [k₁ .x24 (by decide), hp .x24 (by decide)]
  have a00 : u₂.getMem (v.getReg .x10 + BitVec.ofNat 64 (56 * 0)) = y.getReg .x8 := by
    rw [show v.getReg .x10 + BitVec.ofNat 64 (56 * 0) = u₁.getReg .x10 by rw [x10₁]; simp,
      b80006ea0_m_x10_0 h₂, r8]
  have a08 : u₂.getMem (v.getReg .x10 + BitVec.ofNat 64 (56 * 0 + 8)) = y.getReg .x21 :=
    (mx 8).trans ((b80006ea0_m_x10_8 h₂).trans r21)
  have a10 : u₂.getMem (v.getReg .x10 + BitVec.ofNat 64 (56 * 1)) = y.getReg .x19 :=
    (mx 56).trans ((b80006ea0_m_x10_56 h₂).trans r19)
  have a18 : u₂.getMem (v.getReg .x10 + BitVec.ofNat 64 (56 * 1 + 8)) = y.getReg .x23 :=
    (mx 64).trans ((b80006ea0_m_x10_64 h₂).trans r23)
  have a20 : u₂.getMem (v.getReg .x10 + BitVec.ofNat 64 (56 * 2)) = y.getReg .x27 :=
    (mx 112).trans ((b80006ea0_m_x10_112 h₂).trans r27)
  have a28 : u₂.getMem (v.getReg .x10 + BitVec.ofNat 64 (56 * 2 + 8)) = y.getReg .x24 :=
    (mx 120).trans ((b80006ea0_m_x10_120 h₂).trans r24)
  have C0 : ClaimAt s u₂ (v.getReg .x10 + BitVec.ofNat 64 (56 * 0))
      ⟨memory0, state.point.take (logMem s).toNat, mem.getD 0 0⟩ := by
    refine (hc P.c0).claimAt' hlo' (P.c0Lo.mono st₂.mono) a00 a08 ((mx 16).trans ((b80006ea0_m_x10_16 h₂).trans lm₁))
      ?_ ?_
    · rw [mx 24]
      exact (congrArg BitVec.toNat (b80006ea0_m_x10_24 h₂)).trans rfl
    · rw [← P.m0]
      exact eAt_off ((mx 32).trans ((b80006ea0_m_x10_32 h₂).trans m736.1))
        ((mx 40).trans ((b80006ea0_m_x10_40 h₂).trans m736.2.1))
        ((mx 48).trans ((b80006ea0_m_x10_48 h₂).trans m736.2.2))
  have C1 : ClaimAt s u₂ (v.getReg .x10 + BitVec.ofNat 64 (56 * 1))
      ⟨memory1, state.point.take (logMem s).toNat, mem.getD 1 0⟩ := by
    refine (hc P.c1).claimAt' hlo' (P.c1Lo.mono st₂.mono) a10 a18 ((mx 72).trans ((b80006ea0_m_x10_72 h₂).trans lm₁))
      ?_ ?_
    · rw [mx 80]
      exact (congrArg BitVec.toNat (b80006ea0_m_x10_80 h₂)).trans rfl
    · rw [← P.m1]
      exact eAt_off ((mx 88).trans ((b80006ea0_m_x10_88 h₂).trans m1096.1))
        ((mx 96).trans ((b80006ea0_m_x10_96 h₂).trans m1096.2.1))
        ((mx 104).trans ((b80006ea0_m_x10_104 h₂).trans m1096.2.2))
  have C2 : ClaimAt s u₂ (v.getReg .x10 + BitVec.ofNat 64 (56 * 2))
      ⟨memory2, state.point.take (logMem s).toNat, mem.getD 2 0⟩ := by
    refine (hc P.c2).claimAt' hlo' (P.c2Lo.mono st₂.mono) a20 a28 ((mx 128).trans ((b80006ea0_m_x10_128 h₂).trans lm₁))
      ?_ ?_
    · rw [mx 136]
      exact (congrArg BitVec.toNat (b80006ea0_m_x10_136 h₂)).trans rfl
    · rw [← P.m2]
      exact eAt_off ((mx 144).trans ((b80006ea0_m_x10_144 h₂).trans m1192.1))
        ((mx 152).trans ((b80006ea0_m_x10_152 h₂).trans m1192.2.1))
        ((mx 160).trans ((b80006ea0_m_x10_160 h₂).trans m1192.2.2))
  have hl3 : (memClaims s state mem).length = 3 := rfl
  have h3 : (3 : Word).toNat = 3 := rfl
  have CS : ClaimsOk s u₂ 3 (v.getReg .x10) 3 (memClaims s state mem) := by
    refine ⟨⟨Nat.le_refl _, ⟨al, Or.inr ⟨?_, ?_⟩⟩, hl3.symm, fun i hi ↦ ?_⟩, fun i hi ↦ ?_⟩
    · simp only [heapNext]; omega
    · simp only [heapNext, hnz]; omega
    · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · exact C0
      · exact C1
      · exact C2
    · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · exact ap P.c0 0 a00 a08
      · exact ap P.c1 1 a10 a18
      · exact ap P.c2 2 a20 a28
  have hd840 : u₂.getMem (s.getReg .x2 - 840) = 3 := by
    rw [show s.getReg .x2 - 840 = u₁.getReg .x2 + 504 by
      rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
    exact b80006ea0_m_x2_504 h₂
  have hd832 : u₂.getMem (s.getReg .x2 - 832) = v.getReg .x10 := by
    rw [show s.getReg .x2 - 832 = u₁.getReg .x2 + 512 by
      rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1], ← x10₁]
    exact b80006ea0_m_x2_512 h₂
  have hd824 : u₂.getMem (s.getReg .x2 - 824) = 3 := by
    rw [show s.getReg .x2 - 824 = u₁.getReg .x2 + 520 by
      rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
    exact b80006ea0_m_x2_520 h₂
  have s2 (x : Word) (hx : (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2 - 840).toNat ∨ (s.getReg .x2 - 816).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2).toNat) : u₂.getMem x = y.getMem x :=
    st₂.slot hpre (fun z hz h' ↦ by rcases hx with hx | hx <;> addr_omega [hz, h', hx, hb1])
      (by rcases hx with hx | hx <;> constructor <;> addr_omega [hb1, hx])
  have hlen : state.point.length = (y.getMem (s.getReg .x2 - 1144)).toNat := by
    rw [← P.point.elems, eListAt_length]
  obtain ⟨w, hrw, hd | ⟨hpcw, Iw, stw, rgw, x21w, x23w, x27w, c3, c3Lo⟩⟩ := copy4 hT hM hpre I₂
    (b80006ea0_pc h₂) (b80006ea0_x1 h₂)
    (by rw [b80006ea0_x10 h₂, sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (b80006ea0_x13 h₂) (b80006ea0_x14 h₂) ((b80006ea0_x11 h₂).trans lm₁)
    ((b80006ea0_x24 h₂).trans lm₁) ((ry .x18 (by decide)).trans P.x18)
    (s2 _ (Or.inl (by constructor <;> addr_omega [hb1]))) (P.point.keepR hpre st₂.toR f840)
    (by rw [← hlen]; exact P.lm)
  · exact ⟨w, hrv.trans (hr₁.trans (hr₂.trans hrw)), Or.inl hd⟩
  have stT := st₂.trans stw
  have fT : FrameW s fun a ↦ Within a (s.getReg .x2 - 840) 24 ∨
      Within a (s.getReg .x2 - BitVec.ofNat 64 608) 24 := fun a ha ↦ by
    rcases ha with ha | ha <;> addr_omega [ha, hb1]
  have kT (x : Word) (hx : (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2 - 840).toNat ∨ (s.getReg .x2 - 816).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2 - 608).toNat ∨ (s.getReg .x2 - 584).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2).toNat) : w.getMem x = y.getMem x :=
    stT.slot hpre (fun z hz h' ↦ by
      rcases hx with hx | hx | hx <;> rcases h' with h' | h' <;> addr_omega [hz, h', hx, hb1])
      (by rcases hx with hx | hx | hx <;> constructor <;> addr_omega [hb1, hx])
  have sw (x : Word) (hx : (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2 - 608).toNat) : w.getMem x = u₂.getMem x :=
    stw.slot hpre (fun z hz h' ↦ by addr_omega [hz, h', hx, hb1])
      (by constructor <;> addr_omega [hb1, hx])
  have rw' (r : Reg) (hr : r ∈ ([.x18, .x20, .x22, .x25, .x26] : List Reg)) :
      w.getReg r = y.getReg r := by
    rw [rgw r (mem_of_mem hr _), ry r (mem_of_mem hr _)]
  have f608 : FrameW s (Within · (s.getReg .x2 - BitVec.ofNat 64 608) 24) := fun a ha ↦ by
    addr_omega [ha, hb1]
  refine ⟨w, hrv.trans (hr₁.trans (hr₂.trans hrw)), Or.inr ⟨hpcw, {
    inv := Iw
    kept := P.kept.step hpre (stT.toR.weaken fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1]))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1])))))))
    claims := by
      rw [sw _ (by constructor <;> addr_omega [hb1]), sw _ (by constructor <;> addr_omega [hb1]),
        sw _ (by constructor <;> addr_omega [hb1]), hd840, hd832, hd824]
      exact CS.keepR hpre stw.toR f608
    len := (sw _ (by constructor <;> addr_omega [hb1])).trans hd824
    c3 := c3
    c3Lo := c3Lo
    x20 := by rw [rw' .x20 (by decide)]; exact P.x20
    x21 := by
      rw [x21w]; exact (s2 _ (Or.inl (by constructor <;> addr_omega [hb1]))).trans P.kept.out
    x23 := by
      rw [x23w]; exact (s2 _ (Or.inl (by constructor <;> addr_omega [hb1]))).trans P.kept.lb
    x24 := by rw [rgw .x24 (by decide), b80006ea0_x24 h₂]; exact lm₁
    x27 := by rw [x27w]; exact (kT _ (Or.inl (by constructor <;> addr_omega [hb1]))).symm
    memory := P.memory.keepR hpre stT.toR fT (by addr_omega [hb1]) fun z hz h' ↦ by
      rcases h' with h' | h' <;> addr_omega [hz, h', hb1]
    values := P.values.keepR hpre stT.toR fT (by addr_omega [hb1]) fun z hz h' ↦ by
      rcases h' with h' | h' <;> addr_omega [hz, h', hb1]
    point := by
      rw [kT _ (Or.inl (by constructor <;> addr_omega [hb1])), kT _ (Or.inl (by constructor <;> addr_omega [hb1])),
        kT _ (Or.inl (by constructor <;> addr_omega [hb1]))]
      exact P.point.keepR hpre stT.toR fT
    valuesPtr := by
      rw [kT _ (Or.inl (by constructor <;> addr_omega [hb1])), P.valuesPtr, vecPtr, vecPtr,
        show s.getReg .x2 - 176 + 8 = s.getReg .x2 - BitVec.ofNat 64 168 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1], kT _ (Or.inr (Or.inr (by constructor <;> addr_omega [hb1])))]
    pushPtr := by rw [kT _ (Or.inl (by constructor <;> addr_omega [hb1]))]; exact P.pushPtr
    lm := P.lm
    lb := P.lb
    mfEq := by
      rw [rw' .x25 (by decide), rw' .x22 (by decide), kT _ (Or.inl (by constructor <;> addr_omega [hb1]))]
      exact P.mfEq
    bfEq := by
      rw [rw' .x26 (by decide), kT _ (Or.inl (by constructor <;> addr_omega [hb1])),
        kT _ (Or.inl (by constructor <;> addr_omega [hb1]))]
      exact P.bfEq
    tracks := P.tracks.keep fun T hT ↦ stT.transcript hpre P.inv fT hT
    pointLo := by
      rw [kT _ (Or.inl (by constructor <;> addr_omega [hb1])),
        kT _ (Or.inl (by constructor <;> addr_omega [hb1]))]
      exact P.pointLo.mono stT.mono }⟩⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
