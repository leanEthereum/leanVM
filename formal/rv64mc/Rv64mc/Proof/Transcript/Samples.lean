/-
  Rv64mc.Proof.Transcript.Samples

  `Transcript::samples` keeps its contract (`Spec.Transcript.Samples.spec`), over any program holding its template,
  from the contracts of `alloc`, `Vec::reserve`, `handle_error` and `Sponge::sample`. The code checks the byte
  count, allocates it (or takes the dangling pointer `8` for none), builds the header in its frame (`sp + 8`:
  capacity, pointer, length `0`), reserves the count (which keeps the header), samples into the block (`loop`, its
  memory `LoopMem`), and copies the header to `sret` (`fin`). As in `selector_point`, `rv_auto` stops at
  `reserve`'s return (instruction 80), where `after_of` turns the two paths into one `After` and `tail` goes on.

  The loop's memory is the entry's but for the function's stack, the block and the transcript's sponge (`Frame`
  with the sponge as `out`), so the transcript at the end is the entry's through its sponge
  (`TranscriptAt.through`).
-/

import Rv64mc.Spec.Transcript.Samples
import Rv64mc.Spec.Transcript.Sample
import Rv64mc.Spec.Runtime.Alloc
import Rv64mc.Spec.Runtime.VecReserve
import Rv64mc.Spec.Runtime.Panic
import Rv64mc.Model.Extra.Samples
import Rv64mc.Proof.Transcript.VecLoop
import Rv64mc.Proof.Multilinear.SelectorPoint
import Rv64mc.Gen.Tmpl.Verifier.Transcript.Transcript.Samples
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Transcript.Samples

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Transcript Rv64mc.Spec.Transcript.Samples
  Rv64mc.Spec.Runtime Rv64mc.Proof.Transcript Rv64mc.Proof.Multilinear Rv64mc.Proof.Layout
open Rv64mc.Gen.Verifier.Transcript.Transcript.Samples (Link tmpl)

/-! ## The loop's memory -/

/-- The memory after `j` challenges: the entry's but for the function's stack, the block and the sponge at `tp`
    (which holds `s`), the function's frame as after `reserve` (`M`), the challenges `xs` at `q`. -/
def LoopMem (env : Env) (m M : MachineState) (top q tp : Word) (t : Model.TState) (j : Nat) (xs : List E)
    (s : Model.SpongeRust) (M' : MachineState) : Prop :=
  env.Frame top (InRange tp Layouts.Sponge.byteSize) m M' ∧ env.Static M' ∧
    (env.next M).toNat ≤ (env.next M').toNat ∧
    (∀ a : Word, top.toNat - 80 ≤ a.toNat → a.toNat < top.toNat → M'.getMem a = M.getMem a) ∧
    SpongeAt M' tp s ∧ (Model.TM.samples j).run t = some (xs, { t with sponge := s }) ∧ xs.length = j ∧
    ∀ k (hk : k < xs.length), M'.getMem (q + BitVec.ofNat 64 (16 * k)) = (Model.limbs xs[k]).1 ∧
      M'.getMem (q + BitVec.ofNat 64 (16 * k) + 8#64) = (Model.limbs xs[k]).2

/-- **One challenge sampled and stored.** -/
theorem mem_step {env : Env} {m M M' Ms : MachineState} {top q tp : Word} {t : Model.TState} {j N : Nat}
    {xs : List E} {s : Model.SpongeRust} {out : Word → Prop} (hfr : env.Fresh m M q (16 * N)) (hj : j < N)
    (hlim : env.stackLimit.toNat + 80 ≤ top.toNat) (htp : top.toNat ≤ tp.toNat)
    (htp2 : tp.toNat + Layouts.Sponge.byteSize < 2 ^ 64) (h : LoopMem env m M top q tp t j xs s M')
    (hf : env.Frame (top + 18446744073709551536#64) out M' Ms) (hout : ∀ b, out b → InRange tp Layouts.Sponge.byteSize b)
    (hs : SpongeAt Ms tp s.sample.2) (hS : env.Static Ms) :
    LoopMem env m M top q tp t (j + 1) (xs ++ [s.sample.1]) s.sample.2
      ((Ms.setMem (q + BitVec.ofNat 64 (16 * j)) (Model.limbs s.sample.1).1).setMem
        (q + BitVec.ofNat 64 (16 * j) + 8#64) (Model.limbs s.sample.1).2) := by
  obtain ⟨hF, -, hn, hk, -, hrun, hlen, he⟩ := h
  have hlay := env.layout
  have h80 : (top + 18446744073709551536#64).toNat = top.toNat - 80 := slot_toNat (by decide) (by omega) (by decide)
  have hFs : env.Frame top (InRange tp Layouts.Sponge.byteSize) m Ms :=
    hF.trans hf (by omega) fun b hb => Or.inr (Or.inr (Or.inr (hout b hb)))
  have hfr1 := hfr.1; have hfr2 := hfr.2
  have hnM := hF.1; have hnMs := hf.1; have hnx := hf.2.1
  have hq : q.toNat + 16 * N < 2 ^ 64 := by have := env.heapEnd.isLt; omega
  have a1 : (q + BitVec.ofNat 64 (16 * j)).toNat = q.toNat + 16 * j := toNat_add_ofNat (by omega)
  have a2 : (q + BitVec.ofNat 64 (16 * j) + 8#64).toNat = q.toNat + 16 * j + 8 := by
    rw [toNat_add_ofNat (k := 8) (by omega), a1]
  have hn1 : env.next (Ms.setMem (q + BitVec.ofNat 64 (16 * j)) (Model.limbs s.sample.1).1) = env.next Ms :=
    next_store_heap (by omega)
  have hn2 : env.next ((Ms.setMem (q + BitVec.ofNat 64 (16 * j)) (Model.limbs s.sample.1).1).setMem
      (q + BitVec.ofNat 64 (16 * j) + 8#64) (Model.limbs s.sample.1).2) = env.next Ms := by
    rw [next_store_heap (by omega), hn1]
  have ne : ∀ x y : Word, x.toNat ≠ y.toNat → x ≠ y := fun x y h e => h (by rw [e])
  have hkeep : ∀ b : Word, q.toNat + 16 * N ≤ b.toNat → ((Ms.setMem (q + BitVec.ofNat 64 (16 * j))
      (Model.limbs s.sample.1).1).setMem (q + BitVec.ofNat 64 (16 * j) + 8#64) (Model.limbs s.sample.1).2).getMem b =
      Ms.getMem b := fun b hb => by
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega))]
  refine ⟨frame_store_heap (frame_store_heap hFs (by omega) (by omega)) (by omega) (by rw [hn1]; omega),
    static_store_heap (static_store_heap hS (by omega)) (by omega), by rw [hn2]; omega, fun a ha1 ha2 => ?_,
    hs.keep htp2 fun b hb => hkeep b (by unfold InRange at hb; omega), Model.samples_snoc j hrun,
    by simp [hlen], fun k hk => ?_⟩
  · rw [hkeep a (by omega), hf.getMem_above (by omega) (by omega) fun ho => by
      have := hout a ho; unfold InRange at this; omega]
    exact hk a ha1 ha2
  · have b1 : (q + BitVec.ofNat 64 (16 * k)).toNat = q.toNat + 16 * k := toNat_add_ofNat (by simp at hk; omega)
    have b2 : (q + BitVec.ofNat 64 (16 * k) + 8#64).toNat = q.toNat + 16 * k + 8 := by
      rw [toNat_add_ofNat (k := 8) (by simp at hk; omega), b1]
    simp only [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
    · rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
        MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
        List.getElem_append_left hk]
      have hb : ∀ b : Word, b.toNat < (env.next M').toNat → b.toNat < env.heapEnd.toNat →
          Ms.getMem b = M'.getMem b := fun b hb hb' =>
        hf.getMem_below_next (by omega) hb fun ho => by have := hout b ho; unfold InRange at this; omega
      rw [hb _ (by omega) (by omega), hb _ (by omega) (by omega)]
      exact he k hk
    · subst hk
      rw [List.getElem_append_right (by omega)]
      simp only [hlen, Nat.sub_self, List.getElem_singleton]
      exact ⟨by rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq],
        MachineState.getMem_setMem_eq⟩

/-! ## The header copied to `sret` -/

theorem frame_mono {env : Env} {top : Word} {out out' : Word → Prop} {m m' : MachineState}
    (h : env.Frame top out m m') (ho : ∀ b, out b → out' b) : env.Frame top out' m m' := by
  refine ⟨h.1, h.2.1, fun a ha => h.2.2 a fun hw => ha ?_⟩
  rcases hw with hw | hw | hw | hw
  · exact Or.inl hw
  · exact Or.inr (Or.inl hw)
  · exact Or.inr (Or.inr (Or.inl hw))
  · exact Or.inr (Or.inr (Or.inr (ho a hw)))

/-- **The header copied to `sret`** after `N` challenges, from a memory `M'` of the loop over `M`, the memory at
    `reserve`'s return, whose header names the block (capacity `cap`, pointer `q`). -/
theorem fin {env : Env} {m M M' : MachineState} {top q Lw : Word} {regs : Reg → Word} {t : Model.TState}
    {xs : List E} {s : Model.SpongeRust} (hpre : Pre env t regs m) (hx2 : regs .x2 = top)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hlim : env.stackLimit.toNat + 80 ≤ top.toNat)
    (hq : q = M.getMem (top + 18446744073709551552#64))
    (hm : LoopMem env m M top q (regs .x11) t (regs .x12).toNat xs s M') (hL : Lw = BitVec.ofNat 64 xs.length)
    (hcap : xs.length ≤ (M.getMem (top + 18446744073709551544#64)).toNat)
    (hcl : (M.getMem (top + 18446744073709551544#64)).toNat < 2 ^ 63)
    (hfr : (M.getMem (top + 18446744073709551544#64)).toNat = 0 ∨ env.Fresh m M q
      (Layouts.E.byteSize * (M.getMem (top + 18446744073709551544#64)).toNat)) :
    let Mf := ((M'.setMem (regs .x10) (M'.getMem (top + 18446744073709551544#64))).setMem (regs .x10 + 8#64)
      (M'.getMem (top + 18446744073709551552#64))).setMem (regs .x10 + 16#64) Lw
    (∀ a : Word, top.toNat - 80 ≤ a.toNat → a.toNat < top.toNat → Mf.getMem a = M.getMem a) ∧
      env.Frame top (NextScalar.Out Layouts.Vec.byteSize regs m) m Mf ∧ env.Static Mf ∧
      ∀ r, Post env t regs m r Mf := by
  intro Mf
  obtain ⟨ht, hfx1, hfx0, hps, hap1, hap2⟩ := hpre
  rw [hx2] at hfx1 hfx0 hps
  obtain ⟨hF, hS, hnM, hk, hsp, hrun, hlen, he⟩ := hm
  have hlay := env.layout
  have hl0 : env.stackLimit.toNat ≤ top.toNat := by omega
  have hown : env.Owned m top (regs .x10) Layouts.Vec.byteSize := ⟨Or.inr hfx0.1, hfx0.2⟩
  have s0 := owned_slot0 hown hnx hl0 (by decide)
  have s8 := owned_slot (k := 8) hown hnx hl0 (by decide)
  have s16 := owned_slot (k := 16) hown hnx hl0 (by decide)
  have hst : ∀ b : Word, b.toNat < top.toNat → Mf.getMem b = M'.getMem b := fun b h2 => by
    have hne : ∀ c : Word, top.toNat ≤ c.toNat → b ≠ c := fun c hc he => by rw [he] at h2; omega
    have b8 := s8.1.1
    have b16 := s16.1.1
    have b0 := hfx0.1
    simp only [Mf]
    rw [MachineState.getMem_setMem_ne (hne _ (by omega)), MachineState.getMem_setMem_ne (hne _ (by omega)),
      MachineState.getMem_setMem_ne (hne _ hfx0.1)]
  have hnf : env.next Mf = env.next M' := by
    simp only [Mf, Env.next]
    rw [MachineState.getMem_setMem_ne (Ne.symm s16.2.1), MachineState.getMem_setMem_ne (Ne.symm s8.2.1),
      MachineState.getMem_setMem_ne (Ne.symm s0.2.1)]
  have hFo : env.Frame top (NextScalar.Out Layouts.Vec.byteSize regs m) m M' :=
    frame_mono hF fun b hb => Or.inr (Or.inl hb)
  refine ⟨fun a ha1 ha2 => by rw [hst a ha2, hk a ha1 ha2],
    frame_setMem_out (frame_setMem_out (frame_setMem_out hFo (Or.inl s0.1) s0.2.1) (Or.inl s8.1) s8.2.1)
      (Or.inl s16.1) s16.2.1,
    Env.static_setMem (Env.static_setMem (Env.static_setMem hS s0.2.2) s8.2.2) s16.2.2, fun r xs' t' hr => ?_⟩
  rw [hrun] at hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr)
  have e72 : (top + 18446744073709551544#64).toNat = top.toNat - 72 := slot_toNat (by decide) (by omega) (by decide)
  have e64 : (top + 18446744073709551552#64).toNat = top.toNat - 64 := slot_toNat (by decide) (by omega) (by decide)
  refine ⟨⟨q, (M.getMem (top + 18446744073709551544#64)).toNat, ⟨?_, ?_, ?_, by simpa using hcap,
    by simpa using hcl, ?_⟩, ?_⟩, ?_⟩
  · simp only [vecPtr, Layouts.Vec.ptr, Mf]
    rw [MachineState.getMem_setMem_ne (SelectorPoint.ne8_16 _), MachineState.getMem_setMem_eq,
      hk _ (by omega) (by omega), hq]
  · simp only [vecCap, Layouts.Vec.cap, BitVec.add_zero, Mf, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [MachineState.getMem_setMem_ne (SelectorPoint.ne16 _).symm,
      MachineState.getMem_setMem_ne (SelectorPoint.ne8 _).symm, MachineState.getMem_setMem_eq,
      hk _ (by omega) (by omega)]
  · simp only [vecLen, Layouts.Vec.len, Mf, List.length_map]
    rw [MachineState.getMem_setMem_eq, hL]
  · rcases hfr with h | h
    · have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; exact ⟨by simpa using q.isLt, fun k hk => by simp at hk⟩
    · have := h.2; have := hF.2.1; have := env.heapEnd.isLt
      simp only [Layouts.E.byteSize] at *
      refine SelectorPoint.elist_of (by simp only [List.length_map]; omega) fun k hk => ?_
      simp only [List.length_map] at hk
      simp only [List.getElem_map]
      have b1 : (q + BitVec.ofNat 64 (16 * k)).toNat = q.toNat + 16 * k := toNat_add_ofNat (by omega)
      have b2 : (q + BitVec.ofNat 64 (16 * k) + 8#64).toNat = q.toNat + 16 * k + 8 := by
        rw [toNat_add_ofNat (k := 8) (by omega), b1]
      rw [hst _ (by omega), hst _ (by omega)]
      exact he k hk
  · rcases hfr with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h.1, ?_⟩
      have := h.2
      simp only [Layouts.E.byteSize] at *
      rw [hnf]; omega
  · have ht' : TranscriptAt env M' (regs .x11) { t with sponge := s } :=
      ht.through (by simpa using hsp) hfx1.2 hfx1.1 hps hF.1 hnx hl0 fun b hb1 hb2 => by
        rcases hb2 with hb2 | hb2
        · exact hF.getMem_below_next hnx hb2 hb1
        · exact hF.getMem_above hl0 hb2 hb1
    have hb0 := hfx1.2
    simp only [Layouts.Transcript.byteSize] at hb0
    have hpq : proofAddr M' (regs .x11) = proofAddr m (regs .x11) := by
      unfold proofAddr; simp only [Layouts.Transcript.proof]
      have e : (regs .x11 + 328#64).toNat = (regs .x11).toNat + 328 := toNat_add_ofNat (by omega)
      exact hF.getMem_above hl0 (by have := hfx1.1; omega) fun h => by
        unfold InRange at h; simp only [Layouts.Sponge.byteSize] at h; omega
    refine ht'.agree hfx1.2 hF.2.1 fun b hb => ?_
    have hnot : ∀ c, InRange (regs .x10) Layouts.Vec.byteSize c → b ≠ c := fun c hc he => by
      subst he
      rw [hpq] at hb
      unfold InRange at hc
      simp only [Apart, Layouts.Vec.byteSize, Layouts.Transcript.byteSize, Layouts.Proof.byteSize] at hap1 hap2 hb hc
      have := hfx0.1
      rcases hb with hb | hb | hb <;> (try unfold InRange at hb) <;> omega
    simp only [Mf]
    rw [MachineState.getMem_setMem_ne (hnot _ s16.1), MachineState.getMem_setMem_ne (hnot _ s8.1),
      MachineState.getMem_setMem_ne (hnot _ s0.1)]

/-! ## From `reserve`'s return -/

/-- What the function keeps from `reserve`'s return on: its frame from the entry, the saved registers, the header
    (capacity at `sp + 8`, pointer at `sp + 16`, length `0` at `sp + 24`), the block. -/
def After (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (M : MachineState) : Prop :=
  env.Frame top Tactic.F m M ∧ env.Static M ∧
    M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551560#64) = 0#64 ∧ (regs .x12).toNat * 16 < 2 ^ 63 ∧
    ((regs .x12).toNat = 0 ∧ M.getMem (top + 18446744073709551544#64) = 0#64 ∨
      M.getMem (top + 18446744073709551544#64) = regs .x12 ∧
        env.Fresh m M (M.getMem (top + 18446744073709551552#64)) (16 * (regs .x12).toNat))

theorem at72_8 (t : Word) : t + 18446744073709551544#64 + BitVec.ofNat 64 8 = t + 18446744073709551552#64 := by
  rw [BitVec.add_assoc]; rfl
theorem at72_16 (t : Word) : t + 18446744073709551544#64 + BitVec.ofNat 64 16 = t + 18446744073709551560#64 := by
  rw [BitVec.add_assoc]; rfl

/-- **`After` from the header the code stores** (capacity `c`, pointer `q`) over a memory `N` that keeps the
    entry's frame and the saved registers, and `reserve`'s contract. -/
theorem after_of {env : Env} {m N m3 : MachineState} {top ret c q : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 80 ≤ top.toNat) (hF : env.Frame top Tactic.F m N)
    (s8 : N.getMem (top + 18446744073709551608#64) = ret) (s16 : N.getMem (top + 18446744073709551600#64) = regs .x8)
    (s24 : N.getMem (top + 18446744073709551592#64) = regs .x9)
    (s32 : N.getMem (top + 18446744073709551584#64) = regs .x18)
    (s40 : N.getMem (top + 18446744073709551576#64) = regs .x19)
    (s48 : N.getMem (top + 18446744073709551568#64) = regs .x20)
    (h3 : env.Frame (top + 18446744073709551536#64) out
      (((N.setMem (top + 18446744073709551544#64) c).setMem (top + 18446744073709551552#64) q).setMem
        (top + 18446744073709551560#64) 0#64) m3)
    (ho : ∀ b, out b → InRange (top + 18446744073709551544#64) 24 b) (hS3 : env.Static m3)
    (hl3 : vecLen m3 (top + 18446744073709551544#64) = vecLen
      (((N.setMem (top + 18446744073709551544#64) c).setMem (top + 18446744073709551552#64) q).setMem
        (top + 18446744073709551560#64) 0#64) (top + 18446744073709551544#64))
    (hk3 : (regs .x12).toNat ≤ (vecCap
      (((N.setMem (top + 18446744073709551544#64) c).setMem (top + 18446744073709551552#64) q).setMem
        (top + 18446744073709551560#64) 0#64) (top + 18446744073709551544#64)).toNat - (vecLen
      (((N.setMem (top + 18446744073709551544#64) c).setMem (top + 18446744073709551552#64) q).setMem
        (top + 18446744073709551560#64) 0#64) (top + 18446744073709551544#64)).toNat →
      vecCap m3 (top + 18446744073709551544#64) = vecCap
        (((N.setMem (top + 18446744073709551544#64) c).setMem (top + 18446744073709551552#64) q).setMem
          (top + 18446744073709551560#64) 0#64) (top + 18446744073709551544#64) ∧
      vecPtr m3 (top + 18446744073709551544#64) = vecPtr
        (((N.setMem (top + 18446744073709551544#64) c).setMem (top + 18446744073709551552#64) q).setMem
          (top + 18446744073709551560#64) 0#64) (top + 18446744073709551544#64))
    (hb : (regs .x12).toNat * 16 < 2 ^ 63)
    (hc : (regs .x12).toNat = 0 ∧ c = 0#64 ∨ c = regs .x12 ∧ env.Fresh m N q (16 * (regs .x12).toNat)) :
    After env m top ret regs m3 := by
  have e8 : (top + 18446744073709551608#64).toNat = top.toNat - 8 := slot_toNat (by decide) (by omega) (by decide)
  have e48 : (top + 18446744073709551568#64).toNat = top.toNat - 48 := slot_toNat (by decide) (by omega) (by decide)
  have e56 : (top + 18446744073709551560#64).toNat = top.toNat - 56 := slot_toNat (by decide) (by omega) (by decide)
  have e64 : (top + 18446744073709551552#64).toNat = top.toNat - 64 := slot_toNat (by decide) (by omega) (by decide)
  have e72 : (top + 18446744073709551544#64).toNat = top.toNat - 72 := slot_toNat (by decide) (by omega) (by decide)
  have e80 : (top + 18446744073709551536#64).toNat = top.toNat - 80 := slot_toNat (by decide) (by omega) (by decide)
  have r72 : (((N.setMem (top + 18446744073709551544#64) c).setMem (top + 18446744073709551552#64) q).setMem
      (top + 18446744073709551560#64) 0#64).getMem (top + 18446744073709551544#64) = c := by
    rw [MachineState.getMem_setMem_ne (Tactic.add_ne_add (by decide)),
      MachineState.getMem_setMem_ne (Tactic.add_ne_add (by decide)), MachineState.getMem_setMem_eq]
  have r64 : (((N.setMem (top + 18446744073709551544#64) c).setMem (top + 18446744073709551552#64) q).setMem
      (top + 18446744073709551560#64) 0#64).getMem (top + 18446744073709551552#64) = q := by
    rw [MachineState.getMem_setMem_ne (Tactic.add_ne_add (by decide)), MachineState.getMem_setMem_eq]
  simp only [vecCap, vecPtr, vecLen, Layouts.Vec.cap, Layouts.Vec.ptr, Layouts.Vec.len, BitVec.add_zero,
    at72_8, at72_16, MachineState.getMem_setMem_eq, r72, r64] at hl3 hk3
  have hcap : (regs .x12).toNat ≤ c.toNat := by
    rcases hc with h | h
    · omega
    · rw [h.1]
  obtain ⟨hk72, hk64⟩ := hk3 (by simpa using hcap)
  have hin : ∀ b, InRange (top + 18446744073709551544#64) 24 b →
      env.stackLimit.toNat ≤ b.toNat ∧ b.toNat < top.toNat := fun b hb => by unfold InRange at hb; omega
  have f2 : env.Frame top Tactic.F m
      (((N.setMem (top + 18446744073709551544#64) c).setMem (top + 18446744073709551552#64) q).setMem
        (top + 18446744073709551560#64) 0#64) :=
    Tactic.frame_store (Tactic.frame_store (Tactic.frame_store hF (by omega) (by omega)) (by omega) (by omega))
      (by omega) (by omega)
  have f3 := frame_call_own f2 h3 (by omega) fun b hb => hin b (ho b hb)
  have k : ∀ a : Word, top.toNat - 48 ≤ a.toNat → a.toNat < top.toNat → m3.getMem a = N.getMem a :=
    fun a ha1 ha2 => by
      have hn1 : ∀ c : Word, c.toNat < top.toNat - 48 → a ≠ c := fun c hc he => by rw [he] at ha1; omega
      rw [h3.getMem_above (by omega) (by omega) fun hb => by have := ho a hb; unfold InRange at this; omega,
        MachineState.getMem_setMem_ne (hn1 _ (by omega)), MachineState.getMem_setMem_ne (hn1 _ (by omega)),
        MachineState.getMem_setMem_ne (hn1 _ (by omega))]
  have e16 : (top + 18446744073709551600#64).toNat = top.toNat - 16 := slot_toNat (by decide) (by omega) (by decide)
  have e24 : (top + 18446744073709551592#64).toNat = top.toNat - 24 := slot_toNat (by decide) (by omega) (by decide)
  have e32 : (top + 18446744073709551584#64).toNat = top.toNat - 32 := slot_toNat (by decide) (by omega) (by decide)
  have e40 : (top + 18446744073709551576#64).toNat = top.toNat - 40 := slot_toNat (by decide) (by omega) (by decide)
  refine ⟨f3, hS3, by rw [k _ (by omega) (by omega), s8], by rw [k _ (by omega) (by omega), s16],
    by rw [k _ (by omega) (by omega), s24], by rw [k _ (by omega) (by omega), s32],
    by rw [k _ (by omega) (by omega), s40], by rw [k _ (by omega) (by omega), s48], hl3, hb, ?_⟩
  rw [hk72, hk64]
  rcases hc with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h.1, h.2.1, ?_⟩
    have := h.2.2; have := f2.1; have := h3.1
    have hn : env.next (((N.setMem (top + 18446744073709551544#64) c).setMem (top + 18446744073709551552#64)
        q).setMem (top + 18446744073709551560#64) 0#64) = env.next N := by
      rw [Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega)]
    rw [hn] at this; omega

/-- The loop's memory before the first challenge. -/
theorem loopMem_zero {env : Env} {m M : MachineState} {top ret q : Word} {regs : Reg → Word} {t : Model.TState}
    (hpre : Pre env t regs m) (hx2 : regs .x2 = top) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (hA : After env m top ret regs M) :
    LoopMem env m M top q (regs .x11) t 0 [] t.sponge M := by
  obtain ⟨ht, hfx1, -, hps, -, -⟩ := hpre
  rw [hx2] at hfx1 hps
  have ht' := ht.frameF hA.1 hnx hlim hfx1 hps
  exact ⟨Tactic.frame_weaken hA.1, hA.2.1, Nat.le_refl _, fun _ _ _ => rfl, by simpa using ht'.sponge, rfl, rfl,
    fun k hk => by simp at hk⟩

/-! ## The loop -/

/-- The loop's invariant at its head after `j` challenges, `k + 1` to go. -/
def Inv (env : Env) (m M : MachineState) (top q : Word) (regs : Reg → Word) (t : Model.TState) (j k : Nat)
    (xs : List E) (s : Model.SpongeRust) (R : Reg → Word) (M' : MachineState) : Prop :=
  R .x2 = top + 18446744073709551536#64 ∧ R .x8 = BitVec.ofNat 64 (k + 1) ∧ R .x9 = regs .x10 ∧
    R .x18 = regs .x11 ∧ R .x19 = M.getMem (top + 18446744073709551560#64) + regs .x12 ∧
    R .x20 = q + BitVec.ofNat 64 (16 * j) + 8#64 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧
    R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    LoopMem env m M top q (regs .x11) t j xs s M'

/-- The transcript's place and the frame's slots as numbers. -/
theorem facts {env : Env} {t : Model.TState} {regs : Reg → Word} {m : MachineState} {top : Word}
    (hpre : Pre env t regs m) (hx2 : regs .x2 = top) (hlim : env.stackLimit.toNat + 80 ≤ top.toNat) :
    (top.toNat ≤ (regs .x11).toNat ∧ (regs .x11).toNat + 360 < 2 ^ 64) ∧
    (top + 18446744073709551536#64).toNat = top.toNat - 80 ∧ (top + 18446744073709551608#64).toNat = top.toNat - 8 ∧
    (top + 18446744073709551600#64).toNat = top.toNat - 16 ∧ (top + 18446744073709551592#64).toNat = top.toNat - 24 ∧
    (top + 18446744073709551584#64).toNat = top.toNat - 32 ∧ (top + 18446744073709551576#64).toNat = top.toNat - 40 ∧
    (top + 18446744073709551568#64).toNat = top.toNat - 48 := by
  have hfx1 := hpre.2.1
  rw [hx2] at hfx1
  exact ⟨hfx1, slot_toNat (by decide) (by omega) (by decide), slot_toNat (by decide) (by omega) (by decide),
    slot_toNat (by decide) (by omega) (by decide), slot_toNat (by decide) (by omega) (by decide),
    slot_toNat (by decide) (by omega) (by decide), slot_toNat (by decide) (by omega) (by decide),
    slot_toNat (by decide) (by omega) (by decide)⟩

theorem dec_step (k : Nat) :
    BitVec.ofNat 64 (k + 1 + 1) + 18446744073709551615#64 = BitVec.ofNat 64 (k + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem ofNat_ne_zero (k : Nat) (hk : k + 1 < 2 ^ 64) : ¬ BitVec.ofNat 64 (k + 1) = 0#64 := fun h => by
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
  omega

/-- **The loop**, from its head with `k + 1` challenges to go; its last pass copies the header to `sret`. -/
theorem loop (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needS : Nat} (hnS : 80 + needS ≤ need) (hsam : Spec.Transcript.Sample.spec env p L.sample.idx needS)
    {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState} {M : MachineState} {q : Word} {t : Model.TState}
    (hk : ∀ r' m', Holds.post env (Post env t) (NextScalar.Out Layouts.Vec.byteSize) ret top regs m r' m' →
      rvIsa.SafeN p sp1Ctx G n Q ⟨rest, r', m'⟩)
    (hpre : Pre env t regs m) (hx2 : regs .x2 = top)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (htal : top.toNat % 16 = 0) (hA : After env m top ret regs M)
    (hq : q = M.getMem (top + 18446744073709551552#64)) :
    ∀ k j xs s R M', j + k + 1 = (regs .x12).toNat → Inv env m M top q regs t j k xs s R M' →
      rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 94, ret, top⟩ :: rest, R, M'⟩ := by
  have hlim : env.stackLimit.toNat + 80 ≤ top.toNat := by omega
  intro k
  induction k with
  | zero =>
    intro j xs s R M' hj hinv
    have hm : LoopMem env m M top q (regs .x11) t j xs s M' := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2
    rv_intro hinv
    rv_sym hp with [hL] using [hsam s]
    all_goals
      obtain ⟨hfx1, e80, e8, e16, e24, e32, e40, e48⟩ := facts hpre hx2 hlim
      obtain ⟨-, -, a8, a16, a24, a32, a40, a48, a56, hb, hc'⟩ := hA
      have hx12 := (regs .x12).isLt
    · exact hinv_14.2.1
    · omega
    · simp only [Layouts.Sponge.byteSize]; omega
    · exact (hc (by decide)).elim
    all_goals
      have hfr : env.Fresh m M q (16 * (regs .x12).toNat) := by
        rcases hc' with h | h
        · omega
        · rw [hq]; exact h.2
      have ms := mem_step hfr (by omega) hlim (by omega) (by simp only [Layouts.Sponge.byteSize]; omega) hm
        hret1_14 (fun b hb => by
          simp only [Sample.Out, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte] at hb; exact hb)
        hret1_18 hret1_15
      rw [show j + 1 = (regs .x12).toNat by omega] at ms
      have fn := fin (Lw := M.getMem (top + 18446744073709551560#64) + regs .x12) hpre hx2 hnx hlim hq ms
        (by rw [a56, BitVec.zero_add]; apply BitVec.eq_of_toNat_eq; simp; omega)
        (by rcases hc' with h | h
            · omega
            · rw [h.1]; simp; omega)
        (by rcases hc' with h | h
            · omega
            · rw [h.1]; omega)
        (by rcases hc' with h | h
            · omega
            · rw [h.1]; exact Or.inr hfr)
    · rw [fn.1 _ (by omega) (by omega), a8]
    · rw [fn.1 _ (by omega) (by omega), a16]
    · rw [fn.1 _ (by omega) (by omega), a24]
    · rw [fn.1 _ (by omega) (by omega), a32]
    · rw [fn.1 _ (by omega) (by omega), a40]
    · rw [fn.1 _ (by omega) (by omega), a48]
    · exact fn.2.1
    · exact fn.2.2.1
    · exact fn.2.2.2 regs
  | succ k ih =>
    intro j xs s R M' hj hinv
    have hm : LoopMem env m M top q (regs .x11) t j xs s M' := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2
    rv_intro hinv
    rv_sym hp with [hL] using [hsam s]
    all_goals
      obtain ⟨hfx1, e80, e8, e16, e24, e32, e40, e48⟩ := facts hpre hx2 hlim
      obtain ⟨-, -, a8, a16, a24, a32, a40, a48, a56, hb, hc'⟩ := hA
      have hx12 := (regs .x12).isLt
    · exact hinv_14.2.1
    · omega
    · simp only [Layouts.Sponge.byteSize]; omega
    · have hfr : env.Fresh m M q (16 * (regs .x12).toNat) := by
        rcases hc' with h | h
        · omega
        · rw [hq]; exact h.2
      have ms := mem_step hfr (by omega) hlim (by omega) (by simp only [Layouts.Sponge.byteSize]; omega) hm
        hret1_14 (fun b hb => by
          simp only [Sample.Out, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte] at hb; exact hb)
        hret1_18 hret1_15
      refine ih (j + 1) (xs ++ [s.sample.1]) s.sample.2 _ _ (by omega)
        ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ms⟩
      rv_close
      · exact dec_step k
      · exact Multilinear.step_ptr _ _
    all_goals
      have hne := ofNat_ne_zero k (by omega)
      rw [← dec_step k] at hne
      exact absurd hc hne

/-! ## From `reserve`'s return -/

/-- The registers and memory at `reserve`'s return. -/
def TailInv (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551536#64 ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧ R .x18 = regs .x11 ∧
    R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧
    R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧ After env m top ret regs M

/-- **The rest of the function** from `reserve`'s return: the loop, or the empty header copied. -/
theorem tail (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needS : Nat} (hnS : 80 + needS ≤ need) (hsam : Spec.Transcript.Sample.spec env p L.sample.idx needS)
    {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState} {t : Model.TState}
    (hk : ∀ r' m', Holds.post env (Post env t) (NextScalar.Out Layouts.Vec.byteSize) ret top regs m r' m' →
      rvIsa.SafeN p sp1Ctx G n Q ⟨rest, r', m'⟩)
    (hpre : Pre env t regs m) (hx2 : regs .x2 = top)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (htal : top.toNat % 16 = 0) :
    ∀ R M, TailInv env m top ret regs R M → rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 80, ret, top⟩ :: rest, R, M⟩ := by
  have hlim : env.stackLimit.toNat + 80 ≤ top.toNat := by omega
  intro R M hinv
  have hA : After env m top ret regs M := hinv.2.2.2.2.2.2.2.2.2.2.2.2
  rv_intro hinv
  rv_sym hp with [hL]
  all_goals
    obtain ⟨hfx1, e80, e8, e16, e24, e32, e40, e48⟩ := facts hpre hx2 hlim
    obtain ⟨hF, hS, a8, a16, a24, a32, a40, a48, a56, hb, hc'⟩ := id hA
    have hx12 := (regs .x12).isLt
  rotate_right
  · -- the loop
    have hN : 0 < (regs .x12).toNat := by
      have : regs .x12 ≠ 0#64 := hc
      rw [Ne, ← BitVec.toNat_inj] at this; simp at this; omega
    refine loop env p i L hp hL hnS hsam hk hpre hx2 hstk hnx htal hA rfl ((regs .x12).toNat - 1) 0 [] t.sponge _ _
      (by omega) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, loopMem_zero hpre hx2 hnx (by omega) hA⟩
    rv_close
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      omega
    · rw [a56, BitVec.zero_shiftLeft, BitVec.zero_add, Nat.mul_zero, BitVec.add_zero]
  all_goals
    have h0 : (regs .x12).toNat = 0 := by rw [hc]; rfl
    have hcap0 : (M.getMem (top + 18446744073709551544#64)).toNat = 0 := by
      rcases hc' with h | h
      · rw [h.2]; rfl
      · rw [h.1, h0]
    have fn := fin (M' := M) (q := M.getMem (top + 18446744073709551552#64)) (xs := [])
      (Lw := M.getMem (top + 18446744073709551560#64)) hpre hx2 hnx hlim rfl
      (by rw [h0]; exact loopMem_zero hpre hx2 hnx (by omega) hA) (by rw [a56]; rfl) (Nat.zero_le _) (by omega)
      (Or.inl hcap0)
  · rw [fn.1 _ (by omega) (by omega), a8]
  · rw [fn.1 _ (by omega) (by omega), a16]
  · rw [fn.1 _ (by omega) (by omega), a24]
  · rw [fn.1 _ (by omega) (by omega), a32]
  · rw [fn.1 _ (by omega) (by omega), a40]
  · rw [fn.1 _ (by omega) (by omega), a48]
  · exact fn.2.1
  · exact fn.2.2.1
  · exact fn.2.2.2 regs

/-! ## Up to `reserve`'s return -/

/-- The prologue's stores, read back; their frame and `NEXT`. -/
theorem prologue {env : Env} {m : MachineState} {top ret : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 80 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) :
    let M0 := (((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64)
      (regs .x8)).setMem (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64)
      (regs .x18)).setMem (top + 18446744073709551576#64) (regs .x19)).setMem (top + 18446744073709551568#64)
      (regs .x20)
    env.Frame top Tactic.F m M0 ∧ env.next M0 = env.next m ∧
      M0.getMem (top + 18446744073709551608#64) = ret ∧ M0.getMem (top + 18446744073709551600#64) = regs .x8 ∧
      M0.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M0.getMem (top + 18446744073709551584#64) = regs .x18 ∧
      M0.getMem (top + 18446744073709551576#64) = regs .x19 ∧
      M0.getMem (top + 18446744073709551568#64) = regs .x20 := by
  intro M0
  have e8 : (top + 18446744073709551608#64).toNat = top.toNat - 8 := slot_toNat (by decide) (by omega) (by decide)
  have e16 : (top + 18446744073709551600#64).toNat = top.toNat - 16 := slot_toNat (by decide) (by omega) (by decide)
  have e24 : (top + 18446744073709551592#64).toNat = top.toNat - 24 := slot_toNat (by decide) (by omega) (by decide)
  have e32 : (top + 18446744073709551584#64).toNat = top.toNat - 32 := slot_toNat (by decide) (by omega) (by decide)
  have e40 : (top + 18446744073709551576#64).toNat = top.toNat - 40 := slot_toNat (by decide) (by omega) (by decide)
  have e48 : (top + 18446744073709551568#64).toNat = top.toNat - 48 := slot_toNat (by decide) (by omega) (by decide)
  refine ⟨Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store
      (Tactic.frame_store (Tactic.frame_refl hnx) (by omega) (by omega)) (by omega) (by omega)) (by omega) (by omega))
      (by omega) (by omega)) (by omega) (by omega)) (by omega) (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [M0]
    rw [Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega),
      Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega)]
  all_goals simp only [M0]; repeat rw [MachineState.getMem_setMem_ne (Tactic.add_ne_add (by decide))]
  all_goals rw [MachineState.getMem_setMem_eq]

theorem hdr_reads {N : MachineState} {t c q : Word} :
    (((N.setMem (t + 18446744073709551544#64) c).setMem (t + 18446744073709551552#64) q).setMem
        (t + 18446744073709551560#64) 0#64).getMem (t + 18446744073709551544#64) = c := by
  rw [MachineState.getMem_setMem_ne (Tactic.add_ne_add (by decide)),
    MachineState.getMem_setMem_ne (Tactic.add_ne_add (by decide)), MachineState.getMem_setMem_eq]

theorem hdr_reads' {N : MachineState} {t c q : Word} :
    (((N.setMem (t + 18446744073709551544#64) c).setMem (t + 18446744073709551552#64) q).setMem
        (t + 18446744073709551560#64) 0#64).getMem (t + 18446744073709551552#64) = q := by
  rw [MachineState.getMem_setMem_ne (Tactic.add_ne_add (by decide)), MachineState.getMem_setMem_eq]

/-- **`Transcript::samples` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA needR needH needS : Nat} (hnA : 80 + needA ≤ need) (hnR : 80 + needR ≤ need)
    (hnH : 80 + needH ≤ need) (hnS : 80 + needS ≤ need) (hal : AllocSpec env p L.alloc.idx needA)
    (hres : ReserveSpec env 8 16 p L.reserve.idx needR) (hhe : NoReturn env p L.handleError.idx needH)
    (hsam : Spec.Transcript.Sample.spec env p L.sample.idx needS) : spec env p i need := by
  intro t
  rv_auto hp stop [80] with [hL] using [hal, hres, hhe]
  all_goals
    have hlim : env.stackLimit.toNat + 80 ≤ top.toNat := by omega
    have hpre : Pre env t regs m := ⟨hpre_6, ⟨hpre_7, hpre_8⟩, ⟨hpre_9, hpre_10⟩, hpre_11, hpre_12, hpre_13⟩
    have e72 : (top + 18446744073709551544#64).toNat = top.toNat - 72 :=
      slot_toNat (by decide) (by omega) (by decide)
    have e80 : (top + 18446744073709551536#64).toNat = top.toNat - 80 :=
      slot_toNat (by decide) (by omega) (by decide)
    have hov := SelectorPoint.ovf hc_1
    obtain ⟨hF0, hn0, p8, p16, p24, p32, p40, p48⟩ := prologue (ret := ret) (regs := regs) hlim hpre_5
  -- no bytes: the dangling buffer
  · exact Or.inr (by omega)
  · simp only [Layouts.Vec.byteSize]; have := top.isLt; omega
  · exact Or.inr (by omega)
  · simp only [Layouts.RawVecInner.byteSize]; have := top.isLt; omega
  · decide
  · decide
  · decide
  · left; simp only [rvCapAt, Layouts.RawVecInner.cap, BitVec.add_zero]; rw [hdr_reads, hc]; rfl
  · simp only [rvCapAt, Layouts.RawVecInner.cap, BitVec.add_zero]; rw [hdr_reads, hc]; decide
  · simp only [vecLen, Layouts.Vec.len]; rw [at72_16, MachineState.getMem_setMem_eq]; simp
  · refine tail env p i L hp hL hnS hsam hk hpre hpre_2 hpre_3 hpre_5 hpre_14 _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, after_of hlim hF0 p8 p16 p24 p32 p40 p48 hret1_14
      (fun b h => SelectorPoint.grow_in rfl (by omega) h) hret1_15 hret1_16 hret1_17 (by omega) (Or.inl ⟨?_, hc⟩)⟩
    have := hov.1; rw [hc] at this; simp at this; omega
  -- a block from `alloc`
  · rw [hov.1]; omega
  · exact Or.inr (by omega)
  · simp only [Layouts.Vec.byteSize]; have := top.isLt; omega
  · exact Or.inr (by omega)
  · simp only [Layouts.RawVecInner.byteSize]; have := top.isLt; omega
  · decide
  · decide
  · decide
  · right
    simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero, at72_8]
    rw [hdr_reads, hdr_reads']
    have e64 : (top + 18446744073709551552#64).toNat = top.toNat - 64 :=
      slot_toNat (by decide) (by omega) (by decide)
    have e56 : (top + 18446744073709551560#64).toNat = top.toNat - 56 :=
      slot_toNat (by decide) (by omega) (by decide)
    unfold Env.Live
    rw [Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega)]
    rw [hov.1] at hret2_18; omega
  · simp only [rvCapAt, Layouts.RawVecInner.cap, BitVec.add_zero]; rw [hdr_reads]; omega
  · simp only [vecLen, Layouts.Vec.len]; rw [at72_16, MachineState.getMem_setMem_eq]; simp
  · have hF2 := Tactic.frame_call hF0 hret2_14 (by omega)
    have k2 : ∀ a : Word, top.toNat - 80 ≤ a.toNat → m2.getMem a = _ := fun a ha =>
      keep2_1 a (by rw [BitVec.le_def]; omega)
    have e8 : (top + 18446744073709551608#64).toNat = top.toNat - 8 := slot_toNat (by decide) (by omega) (by decide)
    have e16 : (top + 18446744073709551600#64).toNat = top.toNat - 16 :=
      slot_toNat (by decide) (by omega) (by decide)
    have e24 : (top + 18446744073709551592#64).toNat = top.toNat - 24 :=
      slot_toNat (by decide) (by omega) (by decide)
    have e32 : (top + 18446744073709551584#64).toNat = top.toNat - 32 :=
      slot_toNat (by decide) (by omega) (by decide)
    have e40 : (top + 18446744073709551576#64).toNat = top.toNat - 40 :=
      slot_toNat (by decide) (by omega) (by decide)
    have e48 : (top + 18446744073709551568#64).toNat = top.toNat - 48 :=
      slot_toNat (by decide) (by omega) (by decide)
    refine tail env p i L hp hL hnS hsam hk hpre hpre_2 hpre_3 hpre_5 hpre_14 _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, after_of hlim hF2 (by rw [k2 _ (by omega), p8]) (by rw [k2 _ (by omega), p16])
      (by rw [k2 _ (by omega), p24]) (by rw [k2 _ (by omega), p32]) (by rw [k2 _ (by omega), p40])
      (by rw [k2 _ (by omega), p48]) hret3_14 (fun b h => SelectorPoint.grow_in rfl (by omega) h) hret3_15
      hret3_16 hret3_17 (by omega)
      (Or.inr ⟨rfl, by rw [hn0] at hret2_16; exact hret2_16, by rw [hov.1] at hret2_18; omega⟩)⟩

end Rv64mc.Proof.Transcript.Samples
