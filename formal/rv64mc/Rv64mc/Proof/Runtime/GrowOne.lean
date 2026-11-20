/-
  Rv64mc.Proof.Runtime.GrowOne

  `RawVec<T>::grow_one` for every `T` the image keeps, from `grow_amortized`'s and `handle_error`'s contracts: it
  saves `ra`, calls `grow_amortized(self, cap, 1, align, size)`, returns on `Ok` and calls `handle_error`
  otherwise. One proof over the body with `T`'s alignment and size as parameters (`growOneBody`); each instance is
  its template's equation by `rfl`.
-/

import Rv64mc.Spec.Runtime.RawVec
import Rv64mc.Spec.Runtime.Panic
import Rv64mc.Link.Basic

namespace Rv64mc.Proof.Runtime.GrowOne

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime

/-- `grow_one`'s body, for `T` aligned to `align` and of `size` bytes. -/
def growOneBody (base : Word) (s0 s1 : Site) (ga he : Callee) (align size : Nat) : List (LinstrR (Op Reg) Reg) :=
  [.Llabel .internal 0, .Lopn (.set .x2 (.bin .add (.reg .x2) (.imm 0xfffffffffffffff0#64))),
   .Llabel .internal 1, .Lopn (.store .b8 (.bin .add (.reg .x2) (.imm 0x8#64)) (.reg .x1)),
   .Llabel .internal 2, .Lopn (.load .x11 .b8 false (.bin .add (.reg .x10) (.imm 0#64))),
   .Llabel .internal 3, .Lopn (.set .x12 (.bin .add (.imm 0#64) (.imm 1#64))),
   .Llabel .internal 4, .Lopn (.set .x13 (.bin .add (.imm 0#64) (.imm (BitVec.ofNat 64 align)))),
   .Llabel .internal 5, .Lopn (.set .x14 (.bin .add (.imm 0#64) (.imm (BitVec.ofNat 64 size)))),
   .Llabel .internal 6, .Lopn (.set .x1 (.imm s0.hi)),
   .Llabel .internal 7, .Lcall (base + 0x20#64)
     (.indirect (.bin .and (.bin .add (.reg .x1) (.imm s0.lo)) (.imm 0xfffffffffffffffe#64)) [ga.idx]),
   .Llabel .internal 8, .Lopn (.set .x12 (.bin .add (.imm 0#64) (.imm 0xffffffffffffffff#64))),
   .Llabel .internal 9, .Lcond (.cmp "ne" (.reg .x10) (.reg .x12)) 13,
   .Llabel .internal 10, .Lopn (.load .x1 .b8 false (.bin .add (.reg .x2) (.imm 0x8#64))),
   .Llabel .internal 11, .Lopn (.set .x2 (.bin .add (.reg .x2) (.imm 0x10#64))),
   .Llabel .internal 12, .Lret,
   .Llabel .internal 13, .Lopn (.set .x1 (.imm s1.hi)),
   .Llabel .internal 14, .Lcall (base + 0x3c#64)
     (.indirect (.bin .and (.bin .add (.reg .x1) (.imm s1.lo)) (.imm 0xfffffffffffffffe#64)) [he.idx])]

theorem rvCapAt_eq (a : Word) : rvCapAt a = a := by
  simp only [rvCapAt, Layouts.RawVecInner.cap]; exact BitVec.add_zero a

theorem rvPtrAt_eq (a : Word) : rvPtrAt a = a + 8#64 := rfl

/-- A store at or above the stack's limit, outside the header, keeps what `Grown` reads of the state before. -/
theorem grown_of_store {env : Env} {m m' : MachineState} {top a b v : Word} {need size : Nat}
    (hown : env.Owned m top a 16) (hlive : (m.getMem (rvCapAt a)).toNat = 0 ∨
      env.Live m (m.getMem (rvPtrAt a)) ((m.getMem (rvCapAt a)).toNat * size))
    (hb : ¬ InRange a 16 b) (hbs : env.stackLimit.toNat ≤ b.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) :
    Grown env (m.setMem b v) m' a need size → Grown env m m' a need size := by
  have hlay := env.layout
  have h2 := hown.2
  have hc : (m.setMem b v).getMem (rvCapAt a) = m.getMem (rvCapAt a) := by
    have : rvCapAt a ≠ b := fun h => hb (by rw [← h, rvCapAt_eq]; exact ⟨Nat.le_refl _, by omega⟩)
    simp [MachineState.getMem, MachineState.setMem, this]
  have hq : (m.setMem b v).getMem (rvPtrAt a) = m.getMem (rvPtrAt a) := by
    have h8 : (a + 8#64).toNat = a.toNat + 8 := toNat_add_ofNat (by omega)
    have : rvPtrAt a ≠ b := fun h => hb (by rw [← h, rvPtrAt_eq]; exact ⟨by omega, by omega⟩)
    simp [MachineState.getMem, MachineState.setMem, this]
  have hn : env.next (m.setMem b v) = env.next m := Env.next_setMem_stack hbs
  intro hg
  obtain ⟨g1, g2, g3⟩ := hg
  refine ⟨g1, by unfold Env.Fresh at g2 ⊢; rw [hn] at g2; exact g2, fun k hk => ?_⟩
  rw [hc] at g3
  rw [g3 k hk, hq]
  refine getByte_setMem_ne fun he => ?_
  rcases hlive with h0 | hl
  · rw [h0] at hk; omega
  · unfold Env.Live at hl
    have hlt : (m.getMem (rvPtrAt a)).toNat + k < 2 ^ 64 := by
      have := (env.next m).isLt; omega
    have := toNat_alignToDword (m.getMem (rvPtrAt a) + BitVec.ofNat 64 k)
    rw [toNat_add_ofNat hlt, ← he] at this
    have := (env.next m).isLt
    omega

/-- `top - 8`, the slot `ra` is saved in, is not in an owned header. -/
theorem slot_notin {env : Env} {m : MachineState} {top a : Word} (hown : env.Owned m top a 16)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hlim : env.stackLimit.toNat + 16 ≤ top.toNat) :
    ¬ InRange a 16 (top + 0xfffffffffffffff8#64) := by
  have hlay := env.layout
  have h8 : (top + 0xfffffffffffffff8#64).toNat = top.toNat - 8 := by
    rw [BitVec.toNat_add]; have := top.isLt; simp only [BitVec.toNat_ofNat]; omega
  intro hr
  obtain ⟨h1, h2⟩ := hr
  rw [h8] at h1 h2
  rcases hown.1 with h | h
  · omega
  · omega

theorem sp_back : (0xfffffffffffffff0#64 + 0x10#64 : Word) = 0#64 := by decide

/-- **`grow_one`'s contract**, with 16 bytes of stack beyond its callees'. -/
theorem ok {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {fd : Lfundef (Op Reg) Reg} (hp : p[i]? = some fd)
    {base : Word} {s0 s1 : Site} {ga he : Callee} {align size : Nat}
    (hb : fd.body = growOneBody base s0 s1 ga he align size) (hga : ga.WF p) (hhe : he.WF p) (hs0 : s0.WF ga)
    (hs1 : s1.WF he) (halign : align < 2 ^ 63) (hsize : size < 2 ^ 63) {nga : Nat}
    (hGa : GrowAmortizedSpec env p ga.idx nga) (hHe : NoReturn env p he.idx nga) :
    GrowOneSpec env align size p i (16 + nga) := by
  intro G n Q ret top rest regs m ⟨⟨hra, hsp⟩, hstk, hst, hnx, hpre, hal⟩ hk
  obtain ⟨name, addr, depth, body⟩ := fd
  simp only at hb
  subst hb
  simp only [Callee.WF] at hga hhe
  simp only [Site.WF] at hs0 hs1
  lsym hp with [hra, hsp, Lprog.Isa.addrAt, hga, hhe, hs0, hs1, growOneBody, Holds.post, AbiRegs]
    using [hGa.contract, hHe.contract]
  all_goals
    have hlay := env.layout
    obtain ⟨hown, hsz, hal0, hal1, hlive, hcs⟩ := hpre
    rw [hsp] at hown
    have hw : (regs .x10).toNat + 16 < 2 ^ 64 := hown.2
    have h16 : (top + 0xfffffffffffffff0#64).toNat = top.toNat - 16 := by
      rw [BitVec.toNat_add]; have := top.isLt; simp only [BitVec.toNat_ofNat]; omega
    have h8 : (top + 0xfffffffffffffff8#64).toNat = top.toNat - 8 := by
      rw [BitVec.toNat_add]; have := top.isLt; simp only [BitVec.toNat_ofNat]; omega
    have hslot := slot_notin hown hnx (by omega)
    have hb8 : env.stackLimit.toNat ≤ (top + 0xfffffffffffffff8#64).toNat := by rw [h8]; omega
    have hne : regs .x10 ≠ top + 0xfffffffffffffff8#64 := fun h => hslot (by
      rw [← h]; exact ⟨Nat.le_refl _, by have := hown.2; omega⟩)
    have hm1 : (m.setMem (top + 0xfffffffffffffff8#64) ret).getMem (regs .x10) = m.getMem (regs .x10) := by
      simp [MachineState.getMem, MachineState.setMem, hne]
    have hnx1 := Env.next_setMem_stack (env := env) (m := m) (v := ret) hb8
    have hcap1 : (m.setMem (top + 0xfffffffffffffff8#64) ret).getMem (rvCapAt (regs .x10)) =
        m.getMem (rvCapAt (regs .x10)) := by rw [rvCapAt_eq]; exact hm1
    have hneP : rvPtrAt (regs .x10) ≠ top + 0xfffffffffffffff8#64 := fun h => hslot (by
      rw [← h, rvPtrAt_eq]
      exact ⟨by rw [toNat_add_ofNat (by omega)]; omega, by rw [toNat_add_ofNat (by omega)]; omega⟩)
    have hptr1 : (m.setMem (top + 0xfffffffffffffff8#64) ret).getMem (rvPtrAt (regs .x10)) =
        m.getMem (rvPtrAt (regs .x10)) := by
      simp [MachineState.getMem, MachineState.setMem, hneP]
    have hal' : (BitVec.ofNat 64 align).toNat = align := by rw [BitVec.toNat_ofNat]; omega
    have hsz' : (BitVec.ofNat 64 size).toNat = size := by rw [BitVec.toNat_ofNat]; omega
  -- `grow_amortized(self, cap, 1, align, size)`'s precondition
  · refine Holds.pre_call (by show _ ≤ (top + 0xfffffffffffffff0#64).toNat; rw [h16]; omega)
      (Env.static_setMem_stack hst hb8) (by rw [hnx1]; exact hnx) ?_
      (by show (top + 0xfffffffffffffff0#64).toNat % 16 = 0; rw [h16]; omega)
    show GrowPre env (BitVec.ofNat 64 align).toNat (BitVec.ofNat 64 size).toNat _ _
    rw [hal', hsz']
    refine ⟨?_, hsz, hal0, hal1, ?_, ?_⟩
    · show env.Owned _ (top + 0xfffffffffffffff0#64) (regs .x10) _
      exact hown.frame (Env.Frame.setMem_stack (top := top) (out := fun _ => False) hnx hb8 (by rw [h8]; omega))
        (by rw [h16]; omega)
    · show ((m.setMem (top + 0xfffffffffffffff8#64) ret).getMem (rvCapAt (regs .x10))).toNat = 0 ∨
        env.Live (m.setMem (top + 0xfffffffffffffff8#64) ret)
          ((m.setMem (top + 0xfffffffffffffff8#64) ret).getMem (rvPtrAt (regs .x10)))
          (((m.setMem (top + 0xfffffffffffffff8#64) ret).getMem (rvCapAt (regs .x10))).toNat * size)
      rw [hcap1, hptr1]; unfold Env.Live; rw [hnx1]; exact hlive
    · show ((m.setMem (top + 0xfffffffffffffff8#64) ret).getMem (rvCapAt (regs .x10))).toNat * size < 2 ^ 63
      rw [hcap1]; exact hcs
  -- `handle_error`'s precondition, from the stack `grow_amortized` returned
  · refine Holds.pre_call ?_ hret.2.2.1 hret.2.1.2.1 trivial ?_
    · show _ ≤ (r' .x2).toNat
      rw [hret.1.1, h16]; omega
    · show (r' .x2).toNat % 16 = 0
      rw [hret.1.1, h16]; omega
  -- `ra`, read back from its slot, which `grow_amortized` keeps
  · show m'.getMem (top + 0xfffffffffffffff8#64) = ret
    have hout : ¬ GrowOut regs m (top + 0xfffffffffffffff8#64) := by
      rintro (h | h)
      · exact hne (by rw [h, rvCapAt_eq])
      · exact hneP h.symm
    rw [hret.2.1.getMem_above (by rw [h16]; omega) (by rw [h16, h8]; omega) hout]
    exact MachineState.getMem_setMem_eq
  · rfl
  -- the return
  · apply hk
    have hok : Grown env (m.setMem (top + 0xfffffffffffffff8#64) ret) m' (regs .x10)
        (((m.setMem (top + 0xfffffffffffffff8#64) ret).getMem (regs .x10)).toNat + (1#64 : Word).toNat)
        (BitVec.ofNat 64 size).toNat :=
      hret.2.2.2 (by rw [hc])
    rw [hsz', hm1, show m.getMem (regs .x10) = m.getMem (rvCapAt (regs .x10)) by rw [rvCapAt_eq],
      show (1#64 : Word).toNat = 1 from rfl] at hok
    obtain ⟨-, h8', h9', h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := hret.1
    exact ⟨⟨rfl, h8', h9', h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩,
      (Env.Frame.setMem_stack hnx hb8 (by rw [h8]; omega)).trans hret.2.1 (by rw [h16]; omega)
        fun a h => Or.inr (Or.inr (Or.inr h)), hret.2.2.1, grown_of_store hown hlive hslot hb8 hnx hok⟩

end Rv64mc.Proof.Runtime.GrowOne
