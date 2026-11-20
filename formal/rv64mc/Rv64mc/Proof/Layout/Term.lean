/-
  Rv64mc.Proof.Layout.Term

  `Form::term` keeps its contract (`Spec.Layout.Term.spec`) from `alloc`'s and the panic's. `rv_auto` steps the
  body; it reads no load past a store into the heap, so what follows the stores is by hand, over the memory the
  function returns with (`chain`): the block's five words and `sret`'s three, apart from the stack's slots
  (`chain_slot`), within the frame (`chain_frame`), and holding the one-term `Form` (`chain_post`).
-/

import Rv64mc.Spec.Layout.Term
import Rv64mc.Spec.Runtime.Panic
import Rv64mc.Proof.Layout.Out
import Rv64mc.Gen.Tmpl.Verifier.Layout.Form.Term
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Layout.Term

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Layout Rv64mc.Spec.Layout.Term
open Rv64mc.Gen.Verifier.Layout.Form.Term (Link tmpl)

/-- Two words apart by their numbers. -/
macro "addr_ne" : tactic =>
  `(tactic| (intro e; have e' := congrArg BitVec.toNat e; (try simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at e'); omega))

/-- The memory `Form::term` returns with: the term at the block `r` (the monomial's header from `h`, the
    coefficient), then `sret` (`a`) the `Vec` of that one term. -/
def chain (m1 : MachineState) (r a h c0 c1 : Word) : MachineState :=
  (((((((m1.setMem (r + 32#64) c1).setMem r (m1.getMem h)).setMem (r + 8#64) (m1.getMem (h + 8#64))).setMem
    (r + 16#64) (m1.getMem (h + 16#64))).setMem (r + 24#64) c0).setMem a 1#64).setMem (a + 8#64) r).setMem
    (a + 16#64) 1#64

variable {env : Env}

/-- The block lies in the heap, `sret` in the heap below it or above the stack's slots. -/
structure Place (env : Env) (r a : Word) (top : Word) : Prop where
  r_hi : r.toNat + 40 ≤ env.heapEnd.toNat
  a_at : a.toNat + 24 ≤ r.toNat ∨ top.toNat ≤ a.toNat
  a_hi : a.toNat + 24 < 2 ^ 64

/-- **A word above the heap and below the stack's top is not written**: a stack slot, `NEXT`. -/
theorem chain_slot {m1 : MachineState} {r a h c0 c1 top s : Word} (hp : Place env r a top)
    (hs1 : env.heapEnd.toNat ≤ s.toNat) (hs2 : s.toNat < top.toNat) :
    (chain m1 r a h c0 c1).getMem s = m1.getMem s := by
  have := hp.r_hi; have := hp.a_at; have := hp.a_hi
  unfold chain
  repeat rw [MachineState.getMem_setMem_ne (by addr_ne)]

theorem next_chain {m1 : MachineState} {r a h c0 c1 top : Word} (hp : Place env r a top)
    (htop : env.stackLimit.toNat ≤ top.toNat) : env.next (chain m1 r a h c0 c1) = env.next m1 := by
  have := env.layout
  exact chain_slot hp (by omega) (by omega)

theorem chain_static {m1 : MachineState} {r a h c0 c1 top : Word} (hp : Place env r a top)
    (htop : env.stackLimit.toNat ≤ top.toNat) (hs : env.Static m1) : env.Static (chain m1 r a h c0 c1) := by
  have := env.layout
  exact env.static_frame m1 _ (fun x h1 h2 => chain_slot hp (by omega) (by omega)) hs

/-- **The frame**: the block was fresh, `sret` is `out`. -/
theorem chain_frame {m m1 : MachineState} {r a h c0 c1 top : Word} {out : Word → Prop} (hp : Place env r a top)
    (htop : env.stackLimit.toNat ≤ top.toNat) (hF : env.Frame top Tactic.F m m1)
    (hr : (env.next m).toNat ≤ r.toNat) (hr' : r.toNat + 40 = (env.next m1).toNat)
    (ho : ∀ k, k < 24 → out (a + BitVec.ofNat 64 k)) : env.Frame top out m (chain m1 r a h c0 c1) := by
  have := hp.r_hi; have := hp.a_hi
  rw [Env.Frame, next_chain hp htop]
  refine ⟨hF.1, hF.2.1, fun x hx => ?_⟩
  have hf : ∀ k, k < 40 → x ≠ r + BitVec.ofNat 64 k := fun k hk e => hx (Or.inr (Or.inl (by
    rw [e, next_chain hp htop, toNat_add_ofNat (by omega)]; omega)))
  have ha : ∀ k, k < 24 → x ≠ a + BitVec.ofNat 64 k := fun k hk e => hx (Or.inr (Or.inr (Or.inr (e ▸ ho k hk))))
  have e0 := hf 0 (by omega); have e8 := hf 8 (by omega); have e16 := hf 16 (by omega)
  have e24 := hf 24 (by omega); have e32 := hf 32 (by omega)
  have a0 := ha 0 (by omega); have a8 := ha 8 (by omega); have a16 := ha 16 (by omega)
  simp only [BitVec.add_zero] at e0 a0
  unfold chain
  rw [MachineState.getMem_setMem_ne a16, MachineState.getMem_setMem_ne a8, MachineState.getMem_setMem_ne a0,
    MachineState.getMem_setMem_ne e24, MachineState.getMem_setMem_ne e16, MachineState.getMem_setMem_ne e8,
    MachineState.getMem_setMem_ne e0, MachineState.getMem_setMem_ne e32]
  exact hF.2.2 x fun hw => hx (by
    rcases hw with hw | hw | hw | hw
    · exact Or.inl hw
    · exact Or.inr (Or.inl (by rw [next_chain hp htop]; exact hw))
    · exact Or.inr (Or.inr (Or.inl hw))
    · exact hw.elim)

/-- **The one-term `Form` at `sret`**, its monomial's header and buffer read from before the stores. -/
theorem chain_post {m1 : MachineState} {r a h q lo top : Word} {cap : Nat} {ms : List Nat} {c : E}
    (hp : Place env r a top) (hv : VecAt UsizesAt m1 h q cap ms) (hb : BufIn lo (env.next m1) q cap 8)
    (hqr : cap = 0 ∨ q.toNat + 8 * cap ≤ r.toNat) (hqa : cap = 0 ∨ q.toNat + 8 * cap ≤ a.toNat ∨ a.toNat + 24 ≤ q.toNat ∨ top.toNat ≤ a.toNat)
    (hlo : lo.toNat ≤ r.toNat) (hr : r.toNat + 40 ≤ (env.next m1).toNat) (htop : env.stackLimit.toNat ≤ top.toNat) :
    FormIn lo (env.next m1) (chain m1 r a h (Model.limbs c).1 (Model.limbs c).2) a ⟨[(ms, c)]⟩ := by
  have := hp.r_hi; have := hp.a_at; have := hp.a_hi; have := env.layout
  have hlen := hv.len_le
  have hq1 := hv.elems.1
  -- the words of the monomial's buffer are not written
  have keep : Keeps m1 (chain m1 r a h (Model.limbs c).1 (Model.limbs c).2) q (8 * (ms.map (BitVec.ofNat 64)).length) :=
    fun x hx => by
      obtain ⟨hx1, hx2⟩ := hx
      simp only [List.length_map] at hx2
      have hc : cap ≠ 0 := by omega
      have hqr' := hqr.resolve_left hc
      have hqa' := hqa.resolve_left hc
      unfold chain
      repeat rw [MachineState.getMem_setMem_ne (by addr_ne)]
  refine ⟨r, 1, ⟨?_, ?_, ?_, by simp, by norm_num,
    ⟨by simp only [Layouts.VecUsizeE.byteSize, List.length_singleton]; omega, fun k hk => ?_⟩⟩,
    Or.inr ⟨hlo, by simp only [Layouts.VecUsizeE.byteSize]; omega⟩⟩
  · simp only [vecPtr, Layouts.Vec.ptr, chain]
    rw [MachineState.getMem_setMem_ne (by addr_ne), MachineState.getMem_setMem_eq]
  · simp only [vecCap, Layouts.Vec.cap, chain, BitVec.add_zero]
    rw [MachineState.getMem_setMem_ne (by addr_ne), MachineState.getMem_setMem_ne (by addr_ne),
      MachineState.getMem_setMem_eq]
  · simp only [vecLen, Layouts.Vec.len, chain]
    rw [MachineState.getMem_setMem_eq]; rfl
  · simp only [List.length_singleton, Nat.lt_one_iff] at hk
    subst hk
    simp only [List.getElem_singleton, Nat.mul_zero, BitVec.add_zero]
    refine ⟨q, cap, ⟨?_, ?_, ?_, hv.len_le, hv.cap_lt, hv.elems.keep keep⟩, hb, ?_⟩
    · rw [← hv.ptr_eq]
      simp only [vecPtr, Layouts.Vec.ptr, chain]
      repeat rw [MachineState.getMem_setMem_ne (by addr_ne)]
      rw [MachineState.getMem_setMem_eq]
    · rw [← hv.cap_eq]
      simp only [vecCap, Layouts.Vec.cap, chain, BitVec.add_zero]
      repeat rw [MachineState.getMem_setMem_ne (by addr_ne)]
      rw [MachineState.getMem_setMem_eq]
    · rw [← hv.len_eq]
      simp only [vecLen, Layouts.Vec.len, chain]
      repeat rw [MachineState.getMem_setMem_ne (by addr_ne)]
      rw [MachineState.getMem_setMem_eq]
    · simp only [EAt, Layouts.E.c0, Layouts.E.c1, Layouts.VecUsizeE.f1, BitVec.add_zero]
      rw [BitVec.add_assoc, show (24#64 : Word) + 8#64 = 32#64 from rfl]
      unfold chain
      constructor
      · repeat rw [MachineState.getMem_setMem_ne (by addr_ne)]
        rw [MachineState.getMem_setMem_eq]
      · repeat rw [MachineState.getMem_setMem_ne (by addr_ne)]
        rw [MachineState.getMem_setMem_eq]

/-- The monomial's `Vec`, kept from the entry through the prologue and `alloc`. -/
theorem vec_keep {m m1 : MachineState} {top h q lo : Word} {cap : Nat} {ms : List Nat}
    (hF : env.Frame top Tactic.F m m1) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (htop : env.stackLimit.toNat ≤ top.toNat) (hv : VecAt UsizesAt m h q cap ms)
    (hb : BufIn lo (env.next m) q cap 8) (ho : env.Owned m top h Layouts.Vec.byteSize) :
    VecAt UsizesAt m1 h q cap ms := by
  have hlen := hv.len_le
  refine hv.keep (by have := ho.2; simp only [Layouts.Vec.byteSize] at this ⊢; omega) ?_ fun he => he.keep ?_
  · rcases ho.1 with h1 | h1
    · exact Env.Frame.keeps_live hF hnx h1 fun _ _ h => h
    · exact Env.Frame.keeps_above hF htop h1 fun _ _ h => h
  · rcases hb with h0 | ⟨_, h2⟩
    · simp only [List.length_map]; rw [show ms.length = 0 by omega]; intro x hx; unfold InRange at hx; omega
    · exact (Env.Frame.keeps_live hF hnx (show env.Live m q (8 * cap) from h2) fun _ _ h => h).mono (Nat.le_refl _)
        (by simp only [List.length_map]; omega)

theorem next_ne_slot {s : Word} (hs : env.stackLimit.toNat ≤ s.toNat) : env.nextAddr ≠ s := fun e => by
  have := env.layout; rw [← e] at hs; omega

theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (halloc : Spec.Runtime.AllocSpec env p L.alloc.idx 0)
    (hpanic : Spec.Runtime.NoReturn env p L.panicNounwindFmt.idx 0) : spec env p i := by
  intro ms c lo q cap
  rv_auto hp with [hL] using [halloc, hpanic]
  on_goal 1 => decide
  all_goals
    have hlay := env.layout
    have hstk : env.stackLimit.toNat + 48 ≤ top.toNat := hpre_3
    have htop : env.stackLimit.toNat ≤ top.toNat := by omega
    rw [hpre_2] at hpre_11 hpre_13
    have hnp : env.next ((((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64)
        (regs .x8)).setMem (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64)
        (regs .x18)).setMem (top + 18446744073709551576#64) (regs .x19))) = env.next m := by
      unfold Env.next; repeat rw [MachineState.getMem_setMem_ne (next_ne_slot (Tactic.slot_ge hpre_3 (by decide)))]
    rw [hnp] at hret1_16
    have hn1 := hret1_14.2.1
    rw [show (40#64 : Word).toNat = 40 from rfl] at hret1_18
    have hHS : env.heapEnd.toNat ≤ env.stackLimit.toNat := by omega
    have hP : Place env (r1 .x10) (regs .x10) top :=
      ⟨by omega, by simp only [Layouts.Form.byteSize] at hpre_13; omega, hpre_14⟩
    have hF : env.Frame top Tactic.F m m1 := Tactic.frame_call
      (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store
        (Tactic.frame_refl hpre_5) (Tactic.slot_ge hpre_3 (by decide)) (Tactic.slot_lt hpre_3 (by decide)))
        (Tactic.slot_ge hpre_3 (by decide)) (Tactic.slot_lt hpre_3 (by decide))) (Tactic.slot_ge hpre_3 (by decide))
        (Tactic.slot_lt hpre_3 (by decide))) (Tactic.slot_ge hpre_3 (by decide)) (Tactic.slot_lt hpre_3 (by decide)))
        (Tactic.slot_ge hpre_3 (by decide)) (Tactic.slot_lt hpre_3 (by decide))) hret1_14
        (Tactic.slot_le hpre_3 (by decide))
  -- the epilogue's reloads of the saved registers
  any_goals
    refine (chain_slot (h := regs .x11) hP (hHS.trans (Tactic.slot_ge hpre_3 (by decide)))
      (Tactic.slot_lt hpre_3 (by decide))).trans ?_
    rw [keep1_1 _ (Tactic.add_le_add (L := 48) (Tactic.lo_of_room hpre_3) (Tactic.toNat_le_max _) (by decide))]
    repeat rw [MachineState.getMem_setMem_ne (Tactic.add_ne_add (by decide))]
    rw [MachineState.getMem_setMem_eq]
  · exact chain_frame hP htop hF (by omega) (by omega) fun k hk =>
      ⟨by rw [toNat_add_ofNat (by simp only [Layouts.Form.byteSize] at hpre_14; omega)]; omega,
        by rw [toNat_add_ofNat (by simp only [Layouts.Form.byteSize] at hpre_14; omega)]
           simp only [Layouts.Form.byteSize]; omega⟩
  · exact chain_static hP htop hret1_15
  · have hn := hF.1
    show FormIn lo (env.next (chain m1 (r1 .x10) (regs .x10) (regs .x11) (Model.limbs c).1 (Model.limbs c).2))
      (chain m1 (r1 .x10) (regs .x10) (regs .x11) (Model.limbs c).1 (Model.limbs c).2) (regs .x10) ⟨[(ms, c)]⟩
    rw [next_chain hP htop]
    refine chain_post hP (vec_keep hF hpre_5 htop hpre_6 hpre_7 ⟨hpre_11, hpre_12⟩) ?_ ?_ ?_ (by omega) (by omega) htop
    · rcases hpre_7 with h0 | ⟨h1, h2⟩
      · exact Or.inl h0
      · exact Or.inr ⟨h1, by omega⟩
    · rcases hpre_7 with h0 | ⟨h1, h2⟩
      · exact Or.inl h0
      · exact Or.inr (by omega)
    · rcases hpre_7 with h0 | ⟨h1, h2⟩
      · exact Or.inl h0
      · simp only [Layouts.Form.byteSize] at hpre_15; omega

end Rv64mc.Proof.Layout.Term