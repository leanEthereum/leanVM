import Rv64Verifier.Proofs.Pcs.VsoFinalTW
import Rv64Verifier.Proofs.Pcs.VsoFold

/-!
# `verify_stacked_opening`'s final level: a tail round's challenge

The tail's rounds loop at `0x8000b934`: `duplex`, the challenge's lanes to `S - 384` (and `s0`,
`s6`, `s7`), `poly_eval(S - 464, quadratic, S - 384)`, which returns at `0x8000b970`. Registers
through the rounds: `s1` the folds' ladder, `s2` the tail folds' buffer, `s3`/`s4` 24 times / the
rounds done, `s5` `-1`, `s8`/`s9` the transcript and its sponge. The tail folds are a `Vec<E>` at
`S - 304`, the running quadratic at `S - 896` (buffer) and `S - 808` (length).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The tail's round count. -/
abbrev mlF (s : MachineState) (Wl : Model.Pcs.WhirLocals) : ℕ :=
  (s.getReg .x12).toNat - Wl.folds.length

/-- The tail folds `tf`, in a buffer allocated since `u`. -/
def TailV (s u v : MachineState) (tf : List E) : Prop :=
  VecOk v (s.getReg .x2 - 304) 24 8 ∧ vecEs v (s.getReg .x2 - 304) = tf ∧
    NewBuf u v (vecPtr v (s.getReg .x2 - 304)) ((vecCap v (s.getReg .x2 - 304)).toNat * 24) 8

/-- The running quadratic `q`, in the heap since the entry. -/
def QuadAt (s v : MachineState) (q : List E) : Prop :=
  eListAt v (v.getMem (s.getReg .x2 - 896)) (v.getMem (s.getReg .x2 - 808)).toNat = q ∧
    (v.getMem (s.getReg .x2 - 896)).toNat % 8 = 0 ∧
    ((v.getMem (s.getReg .x2 - 808)).toNat = 0 ∨
      heapNext s ≤ (v.getMem (s.getReg .x2 - 896)).toNat ∧
      (v.getMem (s.getReg .x2 - 896)).toNat + 24 * (v.getMem (s.getReg .x2 - 808)).toNat ≤
        heapNext v)

/-- At `0x8000b934`, before tail round `i`: `tf` drawn, the quadratic `q`. -/
structure TR (OA : MachineState → Word → Model.TState → Prop) (s : MachineState) (x : LCtx)
    (u v : MachineState) (Wl : Model.Pcs.WhirLocals) (residual : List E) (i : ℕ)
    (q tf : List E) : Prop extends TI OA s x u v Wl residual where
  pc : v.pc = 0x8000b934
  ilt : i < mlF s Wl
  tfl : tf.length = i
  x9 : v.getReg .x9 = x.FP
  x18 : v.getReg .x18 = vecPtr v (s.getReg .x2 - 304)
  x19 : v.getReg .x19 = BitVec.ofNat 64 (24 * i)
  x20 : v.getReg .x20 = BitVec.ofNat 64 i
  x21 : v.getReg .x21 = 0xffffffffffffffff
  x24 : v.getReg .x24 = s.getReg .x10
  x25 : v.getReg .x25 = s.getReg .x10 + 8
  m168 : v.getMem (s.getReg .x2 - 872) = BitVec.ofNat 64 (mlF s Wl)
  m224 : v.getMem (s.getReg .x2 - 816) = s.getReg .x10
  tail : TailV s u v tf
  quad : QuadAt s v q
  value : RunsF OA s v (Model.TM.sample >>=
    sampledK (cfgOf s) (basisOf s x) residual Wl (mlF s Wl) i q tf)

/-- At `0x8000b970`, round `i`'s challenge `c` at `S - 384` (and in `s0`, `s6`, `s7`), the
quadratic at it in `S - 464`. -/
structure TP (OA : MachineState → Word → Model.TState → Prop) (s : MachineState) (x : LCtx)
    (u v : MachineState) (Wl : Model.Pcs.WhirLocals) (residual : List E) (i : ℕ)
    (q tf : List E) (c : E) : Prop extends TI OA s x u v Wl residual where
  pc : v.pc = 0x8000b970
  ilt : i < mlF s Wl
  tfl : tf.length = i
  x9 : v.getReg .x9 = x.FP
  x18 : v.getReg .x18 = vecPtr v (s.getReg .x2 - 304)
  x19 : v.getReg .x19 = BitVec.ofNat 64 (24 * i)
  x20 : v.getReg .x20 = BitVec.ofNat 64 i
  x21 : v.getReg .x21 = 0xffffffffffffffff
  x24 : v.getReg .x24 = s.getReg .x10
  x25 : v.getReg .x25 = s.getReg .x10 + 8
  m168 : v.getMem (s.getReg .x2 - 872) = BitVec.ofNat 64 (mlF s Wl)
  m224 : v.getMem (s.getReg .x2 - 816) = s.getReg .x10
  tail : TailV s u v tf
  c0 : v.getMem (s.getReg .x2 - 384) = v.getReg .x8
  c1 : v.getMem (s.getReg .x2 - 376) = v.getReg .x22
  c2 : v.getMem (s.getReg .x2 - 368) = v.getReg .x23
  chal : eAt v (s.getReg .x2 - 384) = c
  pe : eAt v (s.getReg .x2 - 464) = Model.polyEvalRust q c
  value : RunsF OA s v (sampledK (cfgOf s) (basisOf s x) residual Wl (mlF s Wl) i q tf c)

/-- The frame's scratch slots, the callees' stacks, the sponge. -/
def SS (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 920) 144 ∨ Within a (s.getReg .x2 - 464) 360 ∨
    Within a (s.getReg .x2 - 2464) 1424 ∨ W s a

section
variable {OA : MachineState → Word → Model.TState → Prop} {s : MachineState} {x : LCtx}
  {u v : MachineState} {Wl : Model.Pcs.WhirLocals} {residual : List E}

/-- A step writing the frame's scratch slots, the callees' stacks or the sponge. -/
theorem TI.stepS (hpre : VsoPre s) (h : TI OA s x u v Wl residual) {w : MachineState}
    {X : Word → Prop} (hX : DFrame v w X)
    (hXs : ∀ a, X a → SS s a) (hsp : w.getReg .x2 = v.getReg .x2) :
    TI OA s x u w Wl residual ∧ w.getMem nextAddr = v.getMem nextAddr := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hf := hI.free
  simp only [Outside] at hf
  have nx : w.getMem nextAddr = v.getMem nextAddr := hX _ fun i hi hw ↦ by
    rcases hXs _ hw with hw | hw | hw | hw
    · addr_omega [hw, hi, hb, hnx]
    · addr_omega [hw, hi, hb, hnx]
    · addr_omega [hw, hi, hb, hnx]
    · simp only [W] at hw; addr_omega [hw, hi, hf.2, hS]
  have hn : heapNext w = heapNext v := by simp only [heapNext, nx]
  refine ⟨h.trans hX (fun a ha ↦ ?_) ⟨by rw [hn]; exact h.heap.lo, by rw [hn]; exact h.heap.hi⟩
    (by rw [hn]) hsp, nx⟩
  rcases hXs _ ha with ha | ha | ha | ha
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ha))))

/-- They miss the heap allocated since the entry. -/
theorem SS.heap (hpre : VsoPre s) {a : Word} (ha : SS s a) {hi : ℕ} (hhi : hi ≤ heapEnd) :
    ¬ (heapNext s ≤ a.toNat ∧ a.toNat < hi) := by
  have hb := bounds hpre
  have hab := hpre.stack.above
  rw [stackLo_vso] at hab
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hf := hI.free
  simp only [Outside] at hf
  simp only [heapEnd] at hhi hab
  intro ⟨h1, h2⟩
  rcases ha with ha | ha | ha | ha
  · addr_omega [ha, hb, h2, hhi, hab]
  · addr_omega [ha, hb, h2, hhi, hab]
  · addr_omega [ha, hb, h2, hhi, hab]
  · simp only [W] at ha
    rcases hf.1 with h0 | h0
    · addr_omega [ha, h0, h1, hS]
    · simp only [heapEnd] at h0; addr_omega [ha, h0, h2, hhi, hS]

/-- The tail folds, kept by a step missing their header and the heap allocated. -/
theorem TailV.keep {tf : List E} {w : MachineState} {X : Word → Prop} (h : TailV s u v tf)
    (hheap : HeapOk v) (hsu : heapNext s ≤ heapNext u) (hX : DFrame v w X)
    (hXa : ∀ a, X a → ¬ Within a (s.getReg .x2 - 304) 24)
    (hXh : ∀ a, X a → ¬ (heapNext s ≤ a.toNat ∧ a.toNat < heapNext v))
    (hb : (s.getReg .x2 - 304).toNat + 24 ≤ 2 ^ 64) (hmono : heapNext v ≤ heapNext w) :
    TailV s u w tf := by
  obtain ⟨hv, he, hn⟩ := h
  have hsm := vec_small hv hheap
  have hk := vecE_keep hX hv (fun a ha ↦ ⟨hXa a ha, fun hw ↦ hXh a ha (by
    rcases hn.2 with h0 | h0
    · simp only [Within] at hw; omega
    · simp only [Within] at hw; omega)⟩) hb hmono hheap
  exact ⟨hk.1, hk.2.1.trans he, by rw [hk.2.2.1, hk.2.2.2.1]; exact NewBuf.grow hn hmono⟩

/-- The quadratic, kept by a step missing its slots and the heap allocated. -/
theorem QuadAt.keep {q : List E} {w : MachineState} {X : Word → Prop} (h : QuadAt s v q)
    (hX : DFrame v w X)
    (hXa : ∀ a, X a → ¬ Within a (s.getReg .x2 - 896) 8 ∧ ¬ Within a (s.getReg .x2 - 808) 8)
    (hXh : ∀ a, X a → ¬ (heapNext s ≤ a.toNat ∧ a.toNat < heapNext v))
    (hb : (s.getReg .x2 - 896).toNat + 8 ≤ 2 ^ 64 ∧ (s.getReg .x2 - 808).toNat + 8 ≤ 2 ^ 64)
    (hhv : heapNext v ≤ heapEnd) (hmono : heapNext v ≤ heapNext w) : QuadAt s w q := by
  obtain ⟨he, h8, hn⟩ := h
  have e1 : w.getMem (s.getReg .x2 - 896) = v.getMem (s.getReg .x2 - 896) :=
    hX.word (fun a ha hx ↦ (hXa a hx).1 ha) hb.1
  have e2 : w.getMem (s.getReg .x2 - 808) = v.getMem (s.getReg .x2 - 808) :=
    hX.word (fun a ha hx ↦ (hXa a hx).2 ha) hb.2
  simp only [heapEnd] at hhv
  refine ⟨?_, by rw [e1]; exact h8, ?_⟩
  · rw [e1, e2, ← he]
    rcases hn with h0 | h0
    · rw [h0]; rfl
    · exact DFrame.eList hX (fun y hy hx ↦ hXh y hx (by simp only [Within] at hy; omega))
        (Or.inr (by omega))
  · rw [e1, e2]
    rcases hn with h0 | h0
    · exact Or.inl h0
    · exact Or.inr ⟨h0.1, by omega⟩

end

theorem tSample (hD : DuplexSpec) (hPE : PolyEvalSpec)
    {OA : MachineState → Word → Model.TState → Prop} {s : MachineState} {x : LCtx}
    {u v : MachineState} {Wl : Model.Pcs.WhirLocals} {residual : List E} {i : ℕ} {q tf : List E}
    (hpre : VsoPre s) (hr : TR OA s x u v Wl residual i q tf) :
    ∃ w, Reaches Image.code v w ∧ (Dead Image.code w ∨
      ∃ c, TP OA s x u w Wl residual i q tf c) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hsp := hr.sp
  have inv := hr.toTI.inv hpre
  -- `0x8000b934`, `duplex`
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000b934_spec hr.pc trivial
  have k₁ := b8000b934_keeps h₁
  have hm₁ := b8000b934_mem_same h₁
  obtain ⟨T₁, n₁⟩ := hr.toTI.stepS hpre (DFrame.of_same hm₁ (fun _ ↦ False)) (fun _ h ↦ h.elim)
    (k₁ .x2 (by decide))
  have inv₁ := T₁.inv hpre
  obtain ⟨t₂, r₂, hv₂⟩ := callDuplex hD hpre inv₁ (b8000b934_pc h₁)
    (by rw [b8000b934_x10 h₁, hr.x25])
  rcases hv₂ with hd | ⟨hpc₂, hpres₂, X₂, hsp₂⟩
  · exact ⟨t₂, r₁.trans r₂, Or.inl hd⟩
  obtain ⟨T₂, n₂⟩ := T₁.stepS hpre X₂ (fun a ha ↦ by
    rcases ha with ha | ha
    · exact Or.inr (Or.inr (Or.inr (by simp only [W]; addr_omega [ha, hS])))
    · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))) (hpres₂ .x2 (by decide))
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := T₂.sp
  have x24₂ : t₂.getReg .x24 = s.getReg .x10 := by
    rw [hpres₂ .x24 (by decide), k₁ .x24 (by decide), hr.x24]
  have inv₂ := T₂.inv hpre
  -- `0x8000b940`: the challenge's lanes, `poly_eval`
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches b8000b940_spec
    (by rw [hpc₂, returnAddress_eq, b8000b934_x1 h₁]; decide) (by
      rv_eval [sp₂, x24₂]
      and_intros <;> first
        | valid_access hst.valid [hb]
        | exact Region.valid hI.ok.self (by addr_omega [hS]) (by addr_omega [hS]) (by addr_omega [hS]))
  have k₃ := b8000b940_keeps h₃
  have X₃ : DFrame t₂ t₃ fun a ↦ Within a (s.getReg .x2 - 384) 24 := by
    have := DFrame.of_memFrame (b8000b940_frame h₃ (by rw [sp₂]; addr_omega [hb]))
    rw [sp₂] at this
    exact this.mono fun a ha ↦ by addr_omega [ha, hb]
  obtain ⟨T₃, n₃⟩ := T₂.stepS hpre X₃ (fun a ha ↦ Or.inr (Or.inl (by addr_omega [ha, hb])))
    (k₃ .x2 (by decide))
  have inv₃ := T₃.inv hpre
  -- the quadratic, kept so far
  have hhv := hr.heap.hi
  have Q₃ : QuadAt s t₃ q := by
    have X : DFrame v t₃ fun a ↦ Within a (s.getReg .x10 + 8) 336 ∨
        Within a (s.getReg .x2 - 1920) 880 ∨ Within a (s.getReg .x2 - 384) 24 :=
      (((DFrame.of_same hm₁ _).trans X₂ fun a ha ↦ by
        rcases ha with ha | ha
        · exact Or.inl ha
        · exact Or.inr (Or.inl ha))).trans X₃ fun a ha ↦ Or.inr (Or.inr ha)
    refine hr.quad.keep X (fun a ha ↦ ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩) (fun a ha ↦ ?_)
      ⟨by addr_omega [hb], by addr_omega [hb]⟩ hhv (by simp only [heapNext, n₃, n₂, n₁]; rfl)
    · rcases ha with ha | ha | ha
      · addr_omega [ha, hw, hIs, hS, hb]
      · addr_omega [ha, hw, hb]
      · addr_omega [ha, hw, hb]
    · rcases ha with ha | ha | ha
      · addr_omega [ha, hw, hIs, hS, hb]
      · addr_omega [ha, hw, hb]
      · addr_omega [ha, hw, hb]
    · refine SS.heap hpre ?_ hhv
      rcases ha with ha | ha | ha
      · exact Or.inr (Or.inr (Or.inr (by simp only [W]; addr_omega [ha, hS])))
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
  -- `poly_eval(S - 464, quadratic, S - 384)`
  have hx11 : t₃.getReg .x11 = t₃.getMem (s.getReg .x2 - 896) := by
    rw [b8000b940_x11 h₃, sp₂, show s.getReg .x2 - BitVec.ofNat 64 1040 + 144 = s.getReg .x2 - 896 by
      addr_omega [hb]]
    exact (X₃.word (fun a ha hx ↦ by addr_omega [ha, hx, hb]) (by addr_omega [hb])).symm
  have hx12 : t₃.getReg .x12 = t₃.getMem (s.getReg .x2 - 808) := by
    rw [b8000b940_x12 h₃, sp₂, show s.getReg .x2 - BitVec.ofNat 64 1040 + 232 = s.getReg .x2 - 808 by
      addr_omega [hb]]
    exact (X₃.word (fun a ha hx ↦ by addr_omega [ha, hx, hb]) (by addr_omega [hb])).symm
  obtain ⟨hqe, hq8, hqb⟩ := Q₃
  have hhs := hpre.heap.lo
  have hn₃ : heapNext t₃ = heapNext v := by simp only [heapNext, n₃, n₂, n₁]
  obtain ⟨t₄, r₄, hv₄⟩ := callPolyEval (o := s.getReg .x2 - 464) (c := s.getReg .x2 - 384)
    hPE hpre inv₃ (b8000b940_pc h₃) (by rw [b8000b940_x10 h₃, sp₂]; addr_omega [hb]) hx11 hx12
    (by rw [b8000b940_x13 h₃, sp₂]; addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
    (by addr_omega [hb]) (by
      rcases hqb with h0 | h0
      · exact Or.inl (by omega)
      · rw [hn₃] at h0
        exact Or.inr ⟨by simp only [heapStart, heapNext] at hhs h0 ⊢; omega,
          by simp only [heapEnd] at hhv ⊢; omega⟩) hq8
  rcases hv₄ with hd | ⟨hpc₄, hpres₄, X₄, hpe⟩
  · exact ⟨t₄, r₁.trans (r₂.trans (r₃.trans r₄)), Or.inl hd⟩
  obtain ⟨T₄, n₄⟩ := T₃.stepS hpre X₄ (fun a ha ↦ by
    rcases ha with ha | ha
    · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
    · exact Or.inr (Or.inr (Or.inl ha))) (hpres₄ .x2 (by decide))
  -- what the round wrote so far, and what it kept
  have X : DFrame v t₄ fun a ↦ Within a (s.getReg .x10 + 8) 336 ∨
      Within a (s.getReg .x2 - 384) 24 ∨ Within a (s.getReg .x2 - 464) 24 ∨
      Within a (s.getReg .x2 - 2464) 1424 :=
    (((DFrame.of_same hm₁ _).trans X₂ fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb])))).trans X₃
        fun a ha ↦ Or.inr (Or.inl ha)).trans X₄ fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ha))
  have hXs (a : Word) (ha : Within a (s.getReg .x10 + 8) 336 ∨
      Within a (s.getReg .x2 - 384) 24 ∨ Within a (s.getReg .x2 - 464) 24 ∨
      Within a (s.getReg .x2 - 2464) 1424) : SS s a := by
    rcases ha with ha | ha | ha | ha
    · exact Or.inr (Or.inr (Or.inr (by simp only [W]; addr_omega [ha, hS])))
    · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
    · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
    · exact Or.inr (Or.inr (Or.inl ha))
  have kw (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 464).toNat ∨ (s.getReg .x2 - 360).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 104).toNat) : t₄.getMem y = v.getMem y :=
    X.word (fun a ha hx ↦ by
      rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy <;>
        addr_omega [ha, hx, hy, hb, hIs, hS]) (by rcases hy with hy | hy <;> addr_omega [hy, hb])
  have hn₄ : heapNext t₄ = heapNext v := by simp only [heapNext, n₄, n₃, n₂, n₁]
  have c₄ : eAt t₄ (s.getReg .x2 - 384) = eAt t₃ (s.getReg .x2 - 384) :=
    X₄.eAt' (fun y hy hx ↦ by rcases hx with hx | hx <;> addr_omega [hy, hx, hb]) (by addr_omega [hb])
  have w₄ (y : Word) (hy : Within y (s.getReg .x2 - 384) 24) : t₄.getMem y = t₃.getMem y :=
    X₄.word (fun a ha hx ↦ by rcases hx with hx | hx <;> addr_omega [ha, hx, hy, hb])
      (by addr_omega [hy, hb])
  have m0 := b8000b940_m_x2_656 h₃
  have m1 := b8000b940_m_x2_664 h₃
  have m2 := b8000b940_m_x2_672 h₃
  rw [sp₂, x24₂] at m0 m1 m2
  have hreg (r : Reg) (h4 : r ∈ calleeSaved) (h3 : t₃.getReg r = t₂.getReg r)
      (h2 : r ∈ calleeSaved) (h1 : t₁.getReg r = v.getReg r) : t₄.getReg r = v.getReg r := by
    rw [hpres₄ r h4, h3, hpres₂ r h2, h1]
  refine ⟨t₄, r₁.trans (r₂.trans (r₃.trans r₄)), Or.inr ⟨eAt t₄ (s.getReg .x2 - 384), {
    toTI := T₄
    pc := by rw [hpc₄, returnAddress_eq, b8000b940_x1 h₃]; decide
    ilt := hr.ilt
    tfl := hr.tfl
    x9 := by rw [hreg .x9 (by decide) (k₃ .x9 (by decide)) (by decide) (k₁ .x9 (by decide)), hr.x9]
    x18 := by
      rw [hreg .x18 (by decide) (k₃ .x18 (by decide)) (by decide) (k₁ .x18 (by decide)), hr.x18]
      simp only [vecPtr]; exact (kw _ (Or.inr (by addr_omega [hb]))).symm
    x19 := by
      rw [hreg .x19 (by decide) (k₃ .x19 (by decide)) (by decide) (k₁ .x19 (by decide)), hr.x19]
    x20 := by
      rw [hreg .x20 (by decide) (k₃ .x20 (by decide)) (by decide) (k₁ .x20 (by decide)), hr.x20]
    x21 := by
      rw [hreg .x21 (by decide) (k₃ .x21 (by decide)) (by decide) (k₁ .x21 (by decide)), hr.x21]
    x24 := by
      rw [hreg .x24 (by decide) (k₃ .x24 (by decide)) (by decide) (k₁ .x24 (by decide)), hr.x24]
    x25 := by
      rw [hreg .x25 (by decide) (k₃ .x25 (by decide)) (by decide) (k₁ .x25 (by decide)), hr.x25]
    m168 := by rw [kw _ (Or.inl (by addr_omega [hb]))]; exact hr.m168
    m224 := by rw [kw _ (Or.inl (by addr_omega [hb]))]; exact hr.m224
    tail := hr.tail.keep hr.heap hr.toTI.fin.su X
      (fun a ha hw ↦ by rcases ha with ha | ha | ha | ha <;> addr_omega [ha, hw, hb, hIs, hS])
      (fun a ha ↦ SS.heap hpre (hXs a ha) hhv) (by addr_omega [hb]) (by rw [hn₄])
    c0 := by
      rw [w₄ (s.getReg .x2 - 384) (by addr_omega [hb]), hpres₄ .x8 (by decide), b8000b940_x8 h₃,
        x24₂, show s.getReg .x2 - 384 = s.getReg .x2 - BitVec.ofNat 64 1040 + 656 by addr_omega [hb]]
      exact m0
    c1 := by
      rw [w₄ (s.getReg .x2 - 376) (by addr_omega [hb]), hpres₄ .x22 (by decide), b8000b940_x22 h₃,
        x24₂, show s.getReg .x2 - 376 = s.getReg .x2 - BitVec.ofNat 64 1040 + 664 by addr_omega [hb]]
      exact m1
    c2 := by
      rw [w₄ (s.getReg .x2 - 368) (by addr_omega [hb]), hpres₄ .x23 (by decide), b8000b940_x23 h₃,
        x24₂, show s.getReg .x2 - 368 = s.getReg .x2 - BitVec.ofNat 64 1040 + 672 by addr_omega [hb]]
      exact m2
    chal := rfl
    pe := by rw [hpe, hqe, c₄]
    value := ?_ }⟩⟩
  refine hr.value.step fun T hT ↦ ?_
  have hT₁ : TranscriptAt t₁ (s.getReg .x10) T :=
    tr_keep hpre inv hT (DFrame.of_same hm₁ (fun _ ↦ False)) (fun _ h ↦ h.elim)
  have hT₂ := tr_duplex hpre inv₁ hT₁ X₂ hsp₂
  have hT₃ := tr_keep hpre inv₂ hT₂ X₃ (fun a ha ↦ Or.inl (by addr_omega [ha, hb]))
  have hT₄ := tr_keep hpre inv₃ hT₃ X₄ (fun a ha ↦ by
    rcases ha with ha | ha
    · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inl (by addr_omega [ha, hb]))
  have hc : (spSqueeze T.sponge).1 = eAt t₄ (s.getReg .x2 - 384) := by
    have hsq : (spSqueeze T.sponge).1 = Compile.challengeOf (spDuplex T.sponge).state := rfl
    rw [hsq, ← hT₁.sponge, ← hsp₂, c₄]
    show Compile.challengeOf (stateAt t₂ (s.getReg .x10 + 8 + 128)) = _
    rw [Samples.challengeOf_stateAt]
    rv_eval [] at m0 m1 m2
    unfold eAt
    rv_eval [m0, m1, m2]
  refine ⟨{ T with sponge := spDuplex T.sponge }, ?_, hT₄⟩
  rw [run_bind_of (show (Model.TM.sample).run T =
    some ((spSqueeze T.sponge).1, { T with sponge := spDuplex T.sponge }) from rfl), hc]

end Rv64Verifier.Proofs.Pcs.Vso
