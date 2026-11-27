/-
  Rv64mc.Proof.Bus.BusLayoutT

  `verifier::bus::bus_layout(framework, blocks)` is total: called with the result's slot (`a0`, 56 bytes: two
  `Vec<Placement>` headers, then the `usize` log), the framework's sizes (`a1`, `a2`, words) and the bus blocks (`a3`,
  `a4`, 48-byte `BusBlock`s), it builds the sizes (a vector of `nb + nf` words, `reserve`d, the framework's copied by
  `memcpy`, each block's `log_rows` pushed by a loop), their offsets (`stack_offsets`), the placements (a block of
  `nb + nf` `(size, offset)` pairs written by a second loop), and splits them after the framework's (`split_off`: a
  second block, `memcpy`). It returns the framework's placements a vector of 16-byte elements of the framework's
  length at the result and the blocks' a vector of the blocks' length at `result + 24`, each buffer fresh unless empty,
  writing only the result's 56 bytes; or the run ends with the guest's abort (`AbortStop`) where a callee or the
  split's check does. A safety-only contract (class D): the placements' values and the log are not stated.

  The precondition asks the result's slot a caller's (`Owned`), in a window and 8-byte aligned, the framework's sizes
  in a window apart from the stack below the stack pointer and below `NEXT` or from the heap's end (`WordsT`: at its
  one caller, `verify_bus_balance`, three words of its frame or none), and the blocks a block allocated before
  (`BufT`: the layout's `push`, `pull` and `count` vectors).

  The body is cut at each label after a call or at a loop's head: 27 (`Inv27`, pc 54), 37 (`Inv37`, pc 74), 45
  (`Inv45`, pc 90), the first loop's head 54 (`L1`, pc 108), 59 (`Inv59`, pc 118), 73 (`Inv73`, pc 146), the second
  loop's head 85 (`L2`, pc 170), 95 (`Inv95`, pc 190), 107 (`Inv107`, pc 214) and 113 (`Inv113`, pc 226), each part
  its own declaration under the default heartbeats. Every part keeps `MemOk` (the slots, the frame, the static data,
  the code); the loops' stores go to blocks allocated since the entry (`heap_store`), their loads need only windows.

  ## Main definitions

  * `WordsT`, `PreT`, `PostT`, `SpecT`, `Slots`, `Saved`, `MemOk`
  * `Inv27`, `Inv37`, `Inv45`, `L1`, `Inv59`, `Inv73`, `L2`, `Inv95`, `Inv107`, `Inv113`: the states at the cuts

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Multilinear.StackOffsetsT
import Rv64mc.Proof.Runtime.ReserveT
import Rv64mc.Proof.Runtime.MemcpyT
import Rv64mc.Proof.Runtime.VecHdrT
import Rv64mc.Gen.Tmpl.Verifier.Bus.BusLayout

namespace Rv64mc.Proof.Bus.BusLayoutT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT RawVecT VecT)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Runtime.ReserveT (ReserveSpecT)
open Rv64mc.Proof.Runtime.MemcpyT (MemcpySpecT)
open Rv64mc.Proof.Runtime.CloneT (ClonePostT)
open Rv64mc.Proof.Runtime.GrowOne (rvCapAt_eq rvPtrAt_eq)
open Rv64mc.Proof.Runtime.VecHdrT (vecCap_eq vecPtr_eq vecLen_eq)
open Rv64mc.Gen.Verifier.Bus.BusLayout (Link tmpl)

/-- A slice of `n` words at `q`: unless empty, in a window, apart from the stack below `sp`, below `NEXT` or from
    the heap's end. -/
def WordsT (env : Env) (m : MachineState) (sp q n : Word) : Prop :=
  n.toNat = 0 ∨ (inWindow q (8 * n.toNat) = true ∧ OffStack env sp q (8 * n.toNat) ∧
    (q.toNat + 8 * n.toNat ≤ (env.next m).toNat ∨ env.heapEnd.toNat ≤ q.toNat))

/-- The total precondition: the result's 56 bytes a caller's, in a window and 8-byte aligned; the framework's sizes
    (`a1`, `a2`) `WordsT`; the bus blocks (`a3`, `a4`) a block of 48-byte elements allocated before (`BufT`). -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) 56 ∧ InWin env (regs .x10) 56 ∧ (regs .x10).toNat % 8 = 0 ∧
    WordsT env m (regs .x2) (regs .x11) (regs .x12) ∧ BufT env m (regs .x14) (regs .x13) 48

/-- The total postcondition: the framework's placements a vector of 16-byte elements of the framework's length at
    the result, the blocks' a vector of the blocks' length at `result + 24`, each buffer fresh unless empty. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 16 ∧ vecLen m' (regs .x10) = regs .x12 ∧
    ((regs .x12).toNat = 0 ∨ env.Fresh m m' (vecPtr m' (regs .x10)) ((regs .x12).toNat * 16)) ∧
    VecT env m' (regs .x10 + 24#64) 16 ∧ vecLen m' (regs .x10 + 24#64) = regs .x14 ∧
    ((regs .x14).toNat = 0 ∨ env.Fresh m m' (vecPtr m' (regs .x10 + 24#64)) ((regs .x14).toNat * 16))

/-- **The total contract of `bus_layout`**: it writes only the result's 56 bytes. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) (Spec.Whir.SretOut 56) AbortStop

/-- The prologue's ten saved words in `M`, at `top - 8` down to `top - 80`. -/
def Slots (M : MachineState) (top ret : Word) (regs : Reg → Word) : Prop :=
  M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551560#64) = regs .x21 ∧ M.getMem (top + 18446744073709551552#64) = regs .x22 ∧
    M.getMem (top + 18446744073709551544#64) = regs .x23 ∧ M.getMem (top + 18446744073709551536#64) = regs .x24

/-- The three saved registers the function does not save, the entry's. -/
def Saved (regs R : Reg → Word) : Prop :=
  R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27

/-- What every part keeps of memory: the slots, the frame, the static data, the code. -/
def MemOk (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (M : MachineState) : Prop :=
  Slots M top ret regs ∧ env.Frame top Tactic.F m M ∧ env.Static M ∧ M.code = m.code

/-- The slots kept by a memory that agrees from `top - 80` up to `top`. -/
theorem slots_keep {M X : MachineState} {top ret : Word} {regs : Reg → Word} (hlim : 80 ≤ top.toNat)
    (hk : ∀ a : Word, top.toNat - 80 ≤ a.toNat → a.toNat < top.toNat → X.getMem a = M.getMem a)
    (hsl : Slots M top ret regs) : Slots X top ret regs := by
  have es : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 80 → X.getMem (top + c) = M.getMem (top + c) :=
    fun c k hc h0 hk' => by
      have e := Runtime.CloneT.toNat_add_neg (t := top) hc (by omega)
      exact hk _ (by rw [e]; omega) (by rw [e]; omega)
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ := hsl
  exact ⟨(es _ 8 rfl (by omega) (by omega)).trans s1, (es _ 16 rfl (by omega) (by omega)).trans s2,
    (es _ 24 rfl (by omega) (by omega)).trans s3, (es _ 32 rfl (by omega) (by omega)).trans s4,
    (es _ 40 rfl (by omega) (by omega)).trans s5, (es _ 48 rfl (by omega) (by omega)).trans s6,
    (es _ 56 rfl (by omega) (by omega)).trans s7, (es _ 64 rfl (by omega) (by omega)).trans s8,
    (es _ 72 rfl (by omega) (by omega)).trans s9, (es _ 80 rfl (by omega) (by omega)).trans s10⟩

/-- `MemOk` kept by a callee's frame from the stack pointer `top - 112`, whose `out` the function may write. -/
theorem memOk_call {env : Env} {m M X : MachineState} {top ret : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 112 ≤ top.toNat) (hM : MemOk env m top ret regs M)
    (hF : env.Frame (top + 18446744073709551504#64) out M X) (hS : env.Static X) (hc : X.code = M.code)
    (hout : ∀ a, out a → (env.next m).toNat ≤ a.toNat ∧ a.toNat < (env.next X).toNat ∨
      (env.stackLimit.toNat ≤ a.toNat ∧ a.toNat < top.toNat - 80)) :
    MemOk env m top ret regs X := by
  have hlay := env.layout
  obtain ⟨hsl, hF0, -, hc0⟩ := hM
  have e112 := Runtime.CloneT.toNat_add_neg (t := top) (c := 18446744073709551504#64) (k := 112) rfl (by omega)
  have hnM := hF.1
  have hnm := hF0.1
  have hnE := hF0.2.1
  have hnX := hF.2.1
  refine ⟨slots_keep (by omega) (fun a h1 h2 => hF.2.2 a fun hw => ?_) hsl,
    hF0.trans hF (by rw [e112]; omega) fun b hb => ?_, hS, hc.trans hc0⟩
  · rcases hw with hw | hw | hw | hw
    · rw [e112] at hw; omega
    · have := hF0.2.1; omega
    · rw [hw] at h1; have := hF0.2.1; omega
    · rcases hout a hw with h | h
      · have := hF0.2.1; omega
      · omega
  · rcases hout b hb with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl ⟨h.1, by omega⟩

/-- The state at instruction 27, after `alloc`: the sizes' block `x10` of `n = nb + nf` words (`x18`, `x11`), none
    when `n = 0`. -/
def Inv27 (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (R : Reg → Word) (M : MachineState) :
    Prop :=
  R .x2 = top + 18446744073709551504#64 ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧ R .x20 = regs .x13 ∧
    R .x21 = regs .x14 ∧ R .x22 = regs .x11 ∧ R .x18 = regs .x14 + regs .x12 ∧ R .x11 = regs .x14 + regs .x12 ∧
    Saved regs R ∧ (R .x18).toNat = (regs .x14).toNat + (regs .x12).toNat ∧ (R .x18).toNat < 2 ^ 30 ∧
    ((R .x18).toNat = 0 ∨ (0x10000000 ≤ (R .x10).toNat ∧ (env.next m).toNat ≤ (R .x10).toNat ∧
      (R .x10).toNat % 8 = 0 ∧ (R .x10).toNat + 8 * (R .x18).toNat ≤ (env.next M).toNat)) ∧
    MemOk env m top ret regs M

/-- The prologue's ten saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  (((((((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)).setMem
    (top + 18446744073709551576#64) (regs .x19)).setMem (top + 18446744073709551568#64) (regs .x20)).setMem
    (top + 18446744073709551560#64) (regs .x21)).setMem (top + 18446744073709551552#64) (regs .x22)).setMem
    (top + 18446744073709551544#64) (regs .x23)).setMem (top + 18446744073709551536#64) (regs .x24)

/-- The prologue's stores: the slots, the frame, the static data and the code. -/
theorem saved_ok {env : Env} {m : MachineState} {top ret : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 112 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hS : env.Static m) : MemOk env m top ret regs (saved m top ret regs) := by
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 112 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e1 := g 18446744073709551608#64 8 rfl (by omega)
  have e2 := g 18446744073709551600#64 16 rfl (by omega)
  have e3 := g 18446744073709551592#64 24 rfl (by omega)
  have e4 := g 18446744073709551584#64 32 rfl (by omega)
  have e5 := g 18446744073709551576#64 40 rfl (by omega)
  have e6 := g 18446744073709551568#64 48 rfl (by omega)
  have e7 := g 18446744073709551560#64 56 rfl (by omega)
  have e8 := g 18446744073709551552#64 64 rfl (by omega)
  have e9 := g 18446744073709551544#64 72 rfl (by omega)
  have e10 := g 18446744073709551536#64 80 rfl (by omega)
  refine ⟨?_, ?_, ?_, by simp only [saved, MachineState.code_setMem]⟩
  · simp only [saved, Slots]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      repeat (first | rw [MachineState.getMem_setMem_eq] | rw [MachineState.getMem_setMem_ne (fun h => by
        have h' := congrArg BitVec.toNat h
        simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10] at h'; omega)])
  · simp only [saved]
    repeat (first | refine Tactic.frame_slot ?_ (by omega) (by omega) | exact Env.Frame.refl hnx)
  · simp only [saved]
    repeat (first | refine Env.static_setMem_stack ?_ (by omega) | exact hS)

/-- The header `(c, P, 0)` stored at `sp`. -/
abbrev hdr (M : MachineState) (top c P : Word) : MachineState :=
  ((M.setMem (top + 18446744073709551504#64) c).setMem (top + 18446744073709551512#64) P).setMem
    (top + 18446744073709551520#64) 0#64

/-- **The sizes' header built**: a vector's of words with no elements over `P` (none when `c = 0`), with `reserve`'s
    buffer condition; `MemOk` and `NEXT` kept. -/
theorem hdr_ok {env : Env} {m M : MachineState} {top ret c P : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 112 ≤ top.toNat) (h16 : top.toNat % 16 = 0) (hW : Windows env top m)
    (hM : MemOk env m top ret regs M) (hc8 : c.toNat * 8 < 2 ^ 63)
    (hP : c.toNat = 0 ∨ (0x10000000 ≤ P.toNat ∧ P.toNat % 8 = 0 ∧ P.toNat + 8 * c.toNat ≤ (env.next M).toNat)) :
    VecT env (hdr M top c P) (top + 18446744073709551504#64) 8 ∧
      (((hdr M top c P).getMem (rvCapAt (top + 18446744073709551504#64))).toNat = 0 ∨
        env.Live (hdr M top c P) ((hdr M top c P).getMem (rvPtrAt (top + 18446744073709551504#64)))
          (((hdr M top c P).getMem (rvCapAt (top + 18446744073709551504#64))).toNat * 8)) ∧
      vecCap (hdr M top c P) (top + 18446744073709551504#64) = c ∧
      vecPtr (hdr M top c P) (top + 18446744073709551504#64) = P ∧
      vecLen (hdr M top c P) (top + 18446744073709551504#64) = 0#64 ∧
      MemOk env m top ret regs (hdr M top c P) ∧ env.next (hdr M top c P) = env.next M := by
  have hlay := env.layout
  have := hW.top_le
  have := hW.next_ge
  obtain ⟨hsl, hF, hS, hc⟩ := hM
  have hnM := hF.2.1
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 112 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e112 := g 18446744073709551504#64 112 rfl (by omega)
  have e104 := g 18446744073709551512#64 104 rfl (by omega)
  have e96 := g 18446744073709551520#64 96 rfl (by omega)
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  have p8 : top + 18446744073709551504#64 + 8#64 = top + 18446744073709551512#64 := by rw [BitVec.add_assoc]; rfl
  have p16 : top + 18446744073709551504#64 + 16#64 = top + 18446744073709551520#64 := by rw [BitVec.add_assoc]; rfl
  have r0 : (hdr M top c P).getMem (top + 18446744073709551504#64) = c := by
    simp only [hdr]
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  have r8 : (hdr M top c P).getMem (top + 18446744073709551512#64) = P := by
    simp only [hdr]
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  have r16 : (hdr M top c P).getMem (top + 18446744073709551520#64) = 0#64 := by
    simp only [hdr]; rw [MachineState.getMem_setMem_eq]
  have hN : env.next (hdr M top c P) = env.next M := by
    simp only [hdr]
    rw [Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega)]
  have hcap : vecCap (hdr M top c P) (top + 18446744073709551504#64) = c := by rw [vecCap_eq, r0]
  have hptr : vecPtr (hdr M top c P) (top + 18446744073709551504#64) = P := by rw [vecPtr_eq, p8, r8]
  have hlen : vecLen (hdr M top c P) (top + 18446744073709551504#64) = 0#64 := by rw [vecLen_eq, p16, r16]
  have hrc : (hdr M top c P).getMem (rvCapAt (top + 18446744073709551504#64)) = c := by rw [rvCapAt_eq, r0]
  have hrp : (hdr M top c P).getMem (rvPtrAt (top + 18446744073709551504#64)) = P := by rw [rvPtrAt_eq, p8, r8]
  have hbuf : BufT env (hdr M top c P) c P 8 := by
    rcases hP with h0 | ⟨h1, h2, h3⟩
    · exact .inl h0
    · exact .inr ⟨h1, by unfold Env.Live; rw [hN]; omega, h2⟩
  refine ⟨⟨.inr ⟨by omega, by simp only [Layouts.Vec.byteSize]; omega⟩,
    ⟨.inr ⟨by omega, by simp only [Layouts.RawVecInner.byteSize]; omega⟩, by omega, by rw [hrc, hrp]; exact hbuf,
      by rw [hrc]; exact hc8⟩, by rw [hlen, hcap]; simp⟩, by rw [hrc, hrp]; exact hbuf.live, hcap, hptr, hlen,
    ⟨slots_keep (by omega) (fun a h1 h2 => by
      simp only [hdr]
      rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
        MachineState.getMem_setMem_ne (ne _ _ (by omega))]) hsl, ?_, ?_, by simp only [hdr, MachineState.code_setMem]; exact hc⟩, hN⟩
  · exact Tactic.frame_slot (Tactic.frame_slot (Tactic.frame_slot hF (by omega) (by omega)) (by omega) (by omega))
      (by omega) (by omega)
  · exact Env.static_setMem_stack (Env.static_setMem_stack (Env.static_setMem_stack hS (by omega)) (by omega))
      (by omega)

/-- The state at instruction 37 (label), the sizes' vector `reserve`d: its buffer `x19`, its length `x23` and `x18`
    zero. -/
def Inv37 (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (R : Reg → Word) (M : MachineState) :
    Prop :=
  R .x2 = top + 18446744073709551504#64 ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧ R .x20 = regs .x13 ∧
    R .x21 = regs .x14 ∧ R .x22 = regs .x11 ∧ R .x23 = 0#64 ∧ R .x18 = 0#64 ∧ Saved regs R ∧
    (regs .x14).toNat + (regs .x12).toNat < 2 ^ 30 ∧
    ((regs .x14).toNat + (regs .x12).toNat = 0 ∨ (0x10000000 ≤ (R .x19).toNat ∧ (env.next m).toNat ≤ (R .x19).toNat ∧
      (R .x19).toNat % 8 = 0 ∧ (R .x19).toNat + 8 * ((regs .x14).toNat + (regs .x12).toNat) ≤ (env.next M).toNat)) ∧
    MemOk env m top ret regs M

set_option rv_sym.heap true in
/-- **From the label 27**: the sizes' header built and `reserve`d. -/
theorem at54 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {needR : Nat} (hre : ReserveSpecT env 8 8 p L.reserve.idx needR)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hnR : env.stackLimit.toNat + 112 + needR ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (h74 : ∀ R M, Inv37 env m top ret regs R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 74, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Inv27 env m top ret regs R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 54, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  obtain ⟨hR2, hR8, hR9, hR20, hR21, hR22, hR18, hR11, hsv, hn, hn30, hP, hM⟩ := hI
  have hlay := env.layout
  have := hW.nextAddr_ge
  have hW1 := hW.heapEnd_le
  have hge := hW.next_ge
  have hnm := hM.2.1.1
  have hlim : env.stackLimit.toNat + 112 ≤ top.toNat := by omega
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 112 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e112 := g 18446744073709551504#64 112 rfl (by omega)
  have e104 := g 18446744073709551512#64 104 rfl (by omega)
  have e96 := g 18446744073709551520#64 96 rfl (by omega)
  rw [hR18] at hn hn30 hP
  have hP0 : (regs .x14 + regs .x12).toNat = 0 ∨ (0x10000000 ≤ (R .x10).toNat ∧ (R .x10).toNat % 8 = 0 ∧
      (R .x10).toNat + 8 * (regs .x14 + regs .x12).toNat ≤ (env.next M).toNat) := by
    rcases hP with h0 | ⟨h1, -, h2, h3⟩
    · exact .inl h0
    · exact .inr ⟨h1, h2, h3⟩
  obtain ⟨hV3, hlv3, hcap3, hptr3, hlen3, hM3, hN3⟩ :=
    hdr_ok (ret := ret) (regs := regs) hlim h16 hW hM (by omega) hP0
  simp only [hdr] at hV3 hlv3 hcap3 hptr3 hlen3 hM3 hN3
  clear hP0
  have hle3 := hV3.2.2
  obtain ⟨hsl3, hF3, hS3, hc3⟩ := hM3
  obtain ⟨-, hF0, -, hc0⟩ := hM
  have hR := And.intro hR2 (And.intro hR8 (And.intro hR9 (And.intro hR20 (And.intro hR21 (And.intro hR22
    (And.intro hR18 (And.intro hR11 hsv)))))))
  rv_introT hR
  rv_symT hp stop [74] with [hL] using [hre]
  have p8 : top + 18446744073709551504#64 + 8#64 = top + 18446744073709551512#64 := by rw [BitVec.add_assoc]; rfl
  have p16 : top + 18446744073709551504#64 + 16#64 = top + 18446744073709551520#64 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨-, hp1⟩ := hret1_17 (by rw [hcap3, hlen3]; simp only [BitVec.toNat_ofNat]; omega)
  have p1 : m1.getMem (top + 18446744073709551512#64) = R .x10 := by rw [← p8, ← vecPtr_eq, hp1, hptr3]
  have l1 : m1.getMem (top + 18446744073709551520#64) = 0#64 := by rw [← p16, ← vecLen_eq, hret1_16, hlen3]
  have hM1 := memOk_call hlim ⟨hsl3, hF3, hS3, hc3⟩ hret1_14 hret1_15 hret1_25 fun b hb => by
    change b = rvCapAt (top + 18446744073709551504#64) ∨ b = rvPtrAt (top + 18446744073709551504#64) at hb
    rw [rvCapAt_eq, rvPtrAt_eq, p8] at hb
    right
    rcases hb with hb | hb <;> rw [hb] <;> omega
  have hn1 := hret1_14.1
  rw [hN3] at hn1
  refine h74 _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, l1, l1, ⟨rfl, rfl, rfl⟩, by omega, ?_, hM1⟩
  simp only [Tactic.rf]
  rw [p1]
  rcases hP with h0 | ⟨h1, h2, h3, h4⟩
  · exact .inl (by omega)
  · exact .inr ⟨h1, h2, h3, by omega⟩

/-- The state at instruction 45 (label), the framework's sizes copied: `x18` the sizes written. -/
def Inv45 (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (R : Reg → Word) (M : MachineState) :
    Prop :=
  R .x2 = top + 18446744073709551504#64 ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧ R .x20 = regs .x13 ∧
    R .x21 = regs .x14 ∧ R .x23 = 0#64 ∧ R .x18 = regs .x12 ∧ Saved regs R ∧
    (regs .x14).toNat + (regs .x12).toNat < 2 ^ 30 ∧
    ((regs .x14).toNat + (regs .x12).toNat = 0 ∨ (0x10000000 ≤ (R .x19).toNat ∧ (env.next m).toNat ≤ (R .x19).toNat ∧
      (R .x19).toNat % 8 = 0 ∧ (R .x19).toNat + 8 * ((regs .x14).toNat + (regs .x12).toNat) ≤ (env.next M).toNat)) ∧
    MemOk env m top ret regs M

set_option rv_sym.heap true in
/-- **From the label 37**: the framework's sizes copied into the sizes' buffer (`memcpy`). -/
theorem at74 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {needM : Nat} (hcp : MemcpySpecT env p L.memcpy.idx needM)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hnM : env.stackLimit.toNat + 112 + needM ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (h2 : regs .x2 = top) (hF : WordsT env m (regs .x2) (regs .x11) (regs .x12))
    (h90 : ∀ R M, Inv45 env m top ret regs R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 90, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Inv37 env m top ret regs R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 74, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  obtain ⟨hR2, hR8, hR9, hR20, hR21, hR22, hR23, hR18, hsv, hn30, hP, hM⟩ := hI
  have hlay := env.layout
  have := hW.nextAddr_ge
  have hW1 := hW.heapEnd_le
  have hge := hW.next_ge
  have hlim : env.stackLimit.toNat + 112 ≤ top.toNat := by omega
  have e112 := Runtime.CloneT.toNat_add_neg (t := top) (c := 18446744073709551504#64) (k := 112) rfl (by omega)
  obtain ⟨hsl, hF0, hS0, hc0⟩ := id hM
  have hnm := hF0.1
  have hnM := hF0.2.1
  rw [h2] at hF
  have hR := And.intro hR2 (And.intro hR8 (And.intro hR9 (And.intro hR20 (And.intro hR21 (And.intro hR22
    (And.intro hR23 (And.intro hR18 hsv)))))))
  rv_introT hR
  rv_symT hp stop [90] with [hL] using [hcp]
  · exact h90 _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, hc.symm, ⟨rfl, rfl, rfl⟩, hn30, hP, hM⟩
  all_goals
    have hnf : (regs .x12).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
    have hs : (regs .x12 <<< 3).toNat = 8 * (regs .x12).toNat := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
    obtain ⟨hP1, hP2, hP3, hP4⟩ := hP.resolve_left (by omega)
    obtain ⟨hs1, hs2, hs3⟩ := hF.resolve_left hnf
    rw [inWindow_iff] at hs1
    unfold OffStack at hs2
  · rw [hs]; omega
  · rw [hs]; omega
  · intro _ b hb1 hb2
    unfold InRange at hb1 hb2
    rw [hs] at hb1 hb2
    omega
  · rw [hs]
    refine .inr ⟨.inl ⟨by omega, by omega⟩, .inl (by omega), by rw [inWindow_iff]; omega, ?_⟩
    unfold OffStack
    rcases hs2 with h | h
    · exact .inl h
    · exact .inr (by rw [e112]; omega)
  · have hM1 := memOk_call hlim hM hret1_14 hret1_15 hret1_19 fun b hb => .inl (by
      have := Runtime.VecHdrT.copyOut_in (P := R .x19) (by exact rfl) (by exact hs) hP3 hb
      have := hret1_14.1
      omega)
    have hn1 := hret1_14.1
    refine h90 _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, hn30, .inr ⟨hP1, hP2, hP3, ?_⟩, hM1⟩
    simp only [Tactic.rf]
    omega

/-- **A store into a block allocated since the entry** keeps `MemOk` and `NEXT`. -/
theorem heap_store {env : Env} {m M : MachineState} {top ret a v : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 112 ≤ top.toNat) (hM : MemOk env m top ret regs M)
    (ha1 : (env.next m).toNat ≤ a.toNat) (ha2 : a.toNat + 8 ≤ (env.next M).toNat) :
    MemOk env m top ret regs (M.setMem a v) ∧ env.next (M.setMem a v) = env.next M := by
  have hlay := env.layout
  obtain ⟨hsl, hF, hS, hc⟩ := hM
  have hnM := hF.2.1
  have hne : a ≠ env.nextAddr := fun e => by rw [e] at ha2; omega
  exact ⟨⟨slots_keep (by omega) (fun b h1 h2 => MachineState.getMem_setMem_ne fun e => by rw [e] at h1 h2; omega) hsl,
    Tactic.frame_fresh hF rfl ha1 (by omega), Tactic.static_store hS (.inl (by omega)),
    by rw [MachineState.code_setMem, hc]⟩, Tactic.next_setMem hne⟩

/-- The state at instruction 59 (label), the sizes written: `x18` their count `nb + nf`, `x19` their buffer. -/
def Inv59 (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (R : Reg → Word) (M : MachineState) :
    Prop :=
  R .x2 = top + 18446744073709551504#64 ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧ Saved regs R ∧
    (R .x18).toNat = (regs .x14).toNat + (regs .x12).toNat ∧ (regs .x14).toNat + (regs .x12).toNat < 2 ^ 30 ∧
    ((regs .x14).toNat + (regs .x12).toNat = 0 ∨ (0x10000000 ≤ (R .x19).toNat ∧ (env.next m).toNat ≤ (R .x19).toNat ∧
      (R .x19).toNat % 8 = 0 ∧ (R .x19).toNat + 8 * ((regs .x14).toNat + (regs .x12).toNat) ≤ (env.next M).toNat)) ∧
    MemOk env m top ret regs M

/-- The first loop's head (label 54) with `k + 1` blocks left: `x20` at the next block's `log_rows` (`B + 24`
    on), `x10` at the next size's word in the sizes' buffer `x19`, `x11` that buffer's end. -/
def L1 (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551504#64 ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧ Saved regs R ∧
    (R .x18).toNat = (regs .x14).toNat + (regs .x12).toNat ∧ (regs .x14).toNat + (regs .x12).toNat < 2 ^ 30 ∧
    k < (regs .x14).toNat ∧ 0x10000000 ≤ (R .x19).toNat ∧ (env.next m).toNat ≤ (R .x19).toNat ∧
    (R .x19).toNat % 8 = 0 ∧ (R .x19).toNat + 8 * ((regs .x14).toNat + (regs .x12).toNat) ≤ (env.next M).toNat ∧
    0x10000000 ≤ (regs .x13).toNat ∧ (regs .x13).toNat % 8 = 0 ∧
    (regs .x13).toNat + 48 * (regs .x14).toNat ≤ (env.next m).toNat ∧
    (R .x11).toNat = (R .x19).toNat + 8 * ((regs .x14).toNat + (regs .x12).toNat) ∧
    (R .x10).toNat = (R .x19).toNat + 8 * ((regs .x12).toNat + ((regs .x14).toNat - 1 - k)) ∧
    (R .x20).toNat = (regs .x13).toNat + 24 + 48 * ((regs .x14).toNat - 1 - k) ∧
    MemOk env m top ret regs M

set_option rv_sym.heap true in
/-- **The first loop**, from its head: each block's `log_rows` pushed to the sizes. -/
theorem loop1 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} (hlim : env.stackLimit.toNat + 112 ≤ top.toNat) (hW : Windows env top m)
    (h16 : top.toNat % 16 = 0)
    (h118 : ∀ R M, Inv59 env m top ret regs R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 118, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, L1 env m top ret regs k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 108, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (L1 env m top ret regs) fun k R M hI ih => ?_
  obtain ⟨hR2, hR8, hR9, hsv, h18, hn30, hk, hP1, hP2, hP3, hP4, hB1, hB8, hB2, h11, h10, h20, hM⟩ := hI
  have hlay := env.layout
  have := hW.nextAddr_ge
  have hW1 := hW.heapEnd_le
  have hge := hW.next_ge
  obtain ⟨hsl, hF0, hS0, hc0⟩ := id hM
  have hnm := hF0.1
  have hnM := hF0.2.1
  have hst := fun v => heap_store (a := R .x10) (v := v) hlim hM (by omega) (by omega)
  have x8 : (R .x10 + 8#64).toNat = (R .x10).toNat + 8 := toNat_add_ofNat (by omega)
  have x48 : (R .x20 + 48#64).toNat = (R .x20).toNat + 48 := toNat_add_ofNat (by omega)
  have hR := And.intro hR2 (And.intro hR8 (And.intro hR9 hsv))
  clear hsl hF0 hS0
  rv_introT hR
  rv_symT hp stop [108, 118] with [_hL]
  · have hk0 : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [x8]; omega))
    refine ih (k - 1) _ _ (by omega) ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, h18, hn30, by omega, hP1, hP2, hP3, ?_, hB1, hB8,
      hB2, h11, ?_, ?_, (hst _).1⟩ <;> simp only [Tactic.rf]
    · rw [(hst _).2]; omega
    · rw [x8]; omega
    · rw [x48]; omega
  · refine h118 _ _ ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, h18, hn30, .inr ⟨hP1, hP2, hP3, ?_⟩, (hst _).1⟩
    simp only [Tactic.rf]
    rw [(hst _).2]; omega

set_option rv_sym.heap true in
/-- **From the label 45**: the blocks' sizes pushed (`loop1`), or none. -/
theorem at90 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} (hW : Windows env top m) (hB : BufT env m (regs .x14) (regs .x13) 48)
    (h118 : ∀ R M, Inv59 env m top ret regs R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 118, ret, top⟩ :: rest, R, M⟩)
    (hl1 : ∀ k R M, L1 env m top ret regs k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 108, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Inv45 env m top ret regs R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 90, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  obtain ⟨hR2, hR8, hR9, hR20, hR21, hR23, hR18, hsv, hn30, hP, hM⟩ := hI
  have hlay := env.layout
  have := hW.nextAddr_ge
  have hW1 := hW.heapEnd_le
  have hge := hW.next_ge
  obtain ⟨hsl, hF0, hS0, hc0⟩ := id hM
  have hnm := hF0.1
  have hnM := hF0.2.1
  have hR := And.intro hR2 (And.intro hR8 (And.intro hR9 (And.intro hR20 (And.intro hR21 (And.intro hR23
    (And.intro hR18 hsv))))))
  rv_introT hR
  rv_symT hp stop [108, 118] with [_hL]
  · refine h118 _ _ ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, ?_, hn30, hP, hM⟩
    simp only [Tactic.rf]
    rw [hc]; simp
  · have hnb : (regs .x14).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
    obtain ⟨hP1, hP2, hP3, hP4⟩ := hP.resolve_left (by omega)
    obtain ⟨hB1, hB2, hB8⟩ := hB.resolve_left hnb
    unfold Env.Live at hB2
    have e12 : (regs .x12 <<< 3).toNat = 8 * (regs .x12).toNat := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
    have e14 : (regs .x14 <<< 3).toNat = 8 * (regs .x14).toNat := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
    refine hl1 ((regs .x14).toNat - 1) _ _ ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, ?_, hn30, by omega, hP1, hP2, hP3, hP4,
      hB1, hB8, by omega, ?_, ?_, ?_, hM⟩ <;> simp only [Tactic.rf, BitVec.toNat_add, e12, e14, BitVec.toNat_ofNat] <;>
      omega

/-- The state at instruction 73 (label), after `stack_offsets`: `x18` the count `nb + nf`, the offsets' buffer at
    `sp + 8` holding that many words, the log in `x22`. -/
def Inv73 (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (R : Reg → Word) (M : MachineState) :
    Prop :=
  R .x2 = top + 18446744073709551504#64 ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧ Saved regs R ∧
    (R .x18).toNat = (regs .x14).toNat + (regs .x12).toNat ∧ (regs .x14).toNat + (regs .x12).toNat < 2 ^ 30 ∧
    ((regs .x14).toNat + (regs .x12).toNat = 0 ∨ (0x10000000 ≤ (R .x19).toNat ∧ (R .x19).toNat % 8 = 0 ∧
      (R .x19).toNat + 8 * ((regs .x14).toNat + (regs .x12).toNat) ≤ (env.next M).toNat ∧
      0x10000000 ≤ (M.getMem (top + 18446744073709551512#64)).toNat ∧
      (M.getMem (top + 18446744073709551512#64)).toNat % 8 = 0 ∧
      (M.getMem (top + 18446744073709551512#64)).toNat + 8 * ((regs .x14).toNat + (regs .x12).toNat) ≤
        (env.next M).toNat)) ∧
    MemOk env m top ret regs M

set_option rv_sym.heap true in
/-- **From the label 59**: the offsets (`stack_offsets`), the count checked. -/
theorem at118 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {needO needH : Nat} (hso : Multilinear.StackOffsetsT.SpecT env p L.stackOffsets.idx needO)
    (hhe : Aborts env p L.handleError.idx needH)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hnO : env.stackLimit.toNat + 112 + needO ≤ top.toNat) (hnH : env.stackLimit.toNat + 112 + needH ≤ top.toNat)
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (h146 : ∀ R M, Inv73 env m top ret regs R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 146, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Inv59 env m top ret regs R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 118, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  obtain ⟨hR2, hR8, hR9, hsv, h18, hn30, hP, hM⟩ := hI
  have hlay := env.layout
  have := hW.nextAddr_ge
  have hW1 := hW.heapEnd_le
  have hge := hW.next_ge
  have hlim : env.stackLimit.toNat + 112 ≤ top.toNat := by omega
  have e112 := Runtime.CloneT.toNat_add_neg (t := top) (c := 18446744073709551504#64) (k := 112) rfl (by omega)
  obtain ⟨hsl, hF0, hS0, hc0⟩ := id hM
  have hnm := hF0.1
  have hnM := hF0.2.1
  have hbuf : BufT env M (R .x18) (R .x19) 8 := by
    rcases hP with h0 | ⟨h1, -, h3, h4⟩
    · exact .inl (by omega)
    · exact .inr ⟨h1, by unfold Env.Live; omega, h3⟩
  have hR := And.intro hR2 (And.intro hR8 (And.intro hR9 hsv))
  rv_introT hR
  rv_symT hp stop [146] with [hL] using [hso, hhe]
  all_goals
    have p8 : top + 18446744073709551504#64 + 8#64 = top + 18446744073709551512#64 := by rw [BitVec.add_assoc]; rfl
    have p16 : top + 18446744073709551504#64 + 16#64 = top + 18446744073709551520#64 := by
      rw [BitVec.add_assoc]; rfl
    have hl : m1.getMem (top + 18446744073709551520#64) = R .x18 := by rw [← hret1_22, vecLen_eq, p16]
    have hM1 := memOk_call hlim hM hret1_14 hret1_15 hret1_24 fun b hb => .inr (by
      change InRange (top + 18446744073709551504#64) 32 b at hb
      unfold InRange at hb; rw [e112] at hb; omega)
    have hn1 := hret1_14.1
    have hle := hret1_21
    rw [vecLen_eq, vecCap_eq, p16, hl] at hle
    have hb := hret1_19
    rw [rvCapAt_eq, rvPtrAt_eq, p8] at hb
    have hP' : (regs .x14).toNat + (regs .x12).toNat = 0 ∨ (0x10000000 ≤ (R .x19).toNat ∧ (R .x19).toNat % 8 = 0 ∧
        (R .x19).toNat + 8 * ((regs .x14).toNat + (regs .x12).toNat) ≤ (env.next m1).toNat ∧
        0x10000000 ≤ (m1.getMem (top + 18446744073709551512#64)).toNat ∧
        (m1.getMem (top + 18446744073709551512#64)).toNat % 8 = 0 ∧
        (m1.getMem (top + 18446744073709551512#64)).toNat + 8 * ((regs .x14).toNat + (regs .x12).toNat) ≤
          (env.next m1).toNat) := by
      rcases hP with h0 | ⟨h1, -, h3, h4⟩
      · exact .inl h0
      · rcases hb with hb | ⟨hb1, hb2, hb3⟩
        · exact .inl (by omega)
        · unfold Env.Live at hb2
          exact .inr ⟨h1, h3, by omega, hb1, hb3, by omega⟩
    clear hb hle hP keep1_1 keep1_2 hret1_14 hret1_16 hret1_17 hret1_19 hret1_20 hret1_21 hret1_22 hret1_23
  · exact h146 _ _ ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, h18, hn30, hP', hM1⟩
  · refine h146 _ _ ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, ?_, hn30, hP', hM1⟩
    simp only [Tactic.rf]
    rw [hl]; exact h18

/-- The state at instruction 95 (label), the placements built: `x20` their buffer `Q` of `n = nb + nf` 16-byte
    elements (`x18`, `x21`), at least `nf`. -/
def Inv95 (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (R : Reg → Word) (M : MachineState) :
    Prop :=
  R .x2 = top + 18446744073709551504#64 ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧ Saved regs R ∧
    (R .x18).toNat = (regs .x14).toNat + (regs .x12).toNat ∧ (R .x21).toNat = (regs .x14).toNat + (regs .x12).toNat ∧
    (regs .x14).toNat + (regs .x12).toNat < 2 ^ 30 ∧ (regs .x12).toNat ≤ (R .x18).toNat ∧
    ((regs .x14).toNat + (regs .x12).toNat = 0 ∨ (0x10000000 ≤ (R .x20).toNat ∧ (env.next m).toNat ≤ (R .x20).toNat ∧
      (R .x20).toNat % 8 = 0 ∧ (R .x20).toNat + 16 * ((regs .x14).toNat + (regs .x12).toNat) ≤ (env.next M).toNat)) ∧
    MemOk env m top ret regs M

/-- The second loop's head (label 85) with `k + 1` placements left: `x19` at the next size in `P`, `x23` at the next
    offset in `O`, `x10` eight bytes into the next placement in `Q` (`x20`), `x11` eight bytes past `Q`'s end. -/
def L2 (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (P O : Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551504#64 ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧ Saved regs R ∧
    (R .x18).toNat = (regs .x14).toNat + (regs .x12).toNat ∧ (regs .x14).toNat + (regs .x12).toNat < 2 ^ 30 ∧
    k < (regs .x14).toNat + (regs .x12).toNat ∧
    0x10000000 ≤ P.toNat ∧ P.toNat % 8 = 0 ∧ P.toNat + 8 * ((regs .x14).toNat + (regs .x12).toNat) ≤ (env.next M).toNat ∧
    0x10000000 ≤ O.toNat ∧ O.toNat % 8 = 0 ∧ O.toNat + 8 * ((regs .x14).toNat + (regs .x12).toNat) ≤ (env.next M).toNat ∧
    0x10000000 ≤ (R .x20).toNat ∧ (env.next m).toNat ≤ (R .x20).toNat ∧ (R .x20).toNat % 8 = 0 ∧
    (R .x20).toNat + 16 * ((regs .x14).toNat + (regs .x12).toNat) ≤ (env.next M).toNat ∧
    (R .x11).toNat = (R .x20).toNat + 8 + 16 * ((regs .x14).toNat + (regs .x12).toNat) ∧
    (R .x10).toNat = (R .x20).toNat + 8 + 16 * ((regs .x14).toNat + (regs .x12).toNat - 1 - k) ∧
    (R .x19).toNat = P.toNat + 8 * ((regs .x14).toNat + (regs .x12).toNat - 1 - k) ∧
    (R .x23).toNat = O.toNat + 8 * ((regs .x14).toNat + (regs .x12).toNat - 1 - k) ∧
    MemOk env m top ret regs M

set_option rv_sym.heap true in
/-- **The second loop**, from its head: each placement `(size, offset)` written, then the split's check. -/
theorem loop2 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {needS : Nat} (hass : Aborts env p L.assertFailed.idx needS)
    {Q : State rvIsa → Prop} {ret top P O : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hnS : env.stackLimit.toNat + 112 + needS ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (h190 : ∀ R M, Inv95 env m top ret regs R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 190, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, L2 env m top ret regs P O k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 170, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (L2 env m top ret regs P O) fun k R M hI ih => ?_
  obtain ⟨hR2, hR8, hR9, hsv, h18, hn30, hk, hP1, hP8, hP2, hO1, hO8, hO2, hQ1, hQ2, hQ8, hQ3, h11, h10, h19, h23,
    hM⟩ := hI
  have hlay := env.layout
  have := hW.nextAddr_ge
  have hW1 := hW.heapEnd_le
  have hge := hW.next_ge
  have hlim : env.stackLimit.toNat + 112 ≤ top.toNat := by omega
  obtain ⟨hsl, hF0, hS0, hc0⟩ := id hM
  have hnm := hF0.1
  have hnM := hF0.2.1
  have x16 : (R .x10 + 16#64).toNat = (R .x10).toNat + 16 := toNat_add_ofNat (by omega)
  have x8 : (R .x19 + 8#64).toNat = (R .x19).toNat + 8 := toNat_add_ofNat (by omega)
  have x8' : (R .x23 + 8#64).toNat = (R .x23).toNat + 8 := toNat_add_ofNat (by omega)
  have xm8 := Runtime.CloneT.toNat_add_neg (t := R .x10) (c := 18446744073709551608#64) (k := 8) rfl (by omega)
  have hs1 := heap_store (a := R .x10 + 18446744073709551608#64) (v := M.getMem (R .x19)) hlim hM
    (by rw [xm8]; omega) (by rw [xm8]; omega)
  have hs2 := heap_store (a := R .x10) (v := M.getMem (R .x23)) hlim hs1.1 (by omega) (by rw [hs1.2]; omega)
  have hR := And.intro hR2 (And.intro hR8 (And.intro hR9 hsv))
  clear hsl hF0
  rv_introT hR
  rv_symT hp stop [170, 190] with [hL] using [hass]
  · have hk0 : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [x16]; omega))
    refine ih (k - 1) _ _ (by omega) ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, h18, hn30, by omega, hP1, hP8, ?_, hO1, hO8, ?_,
      hQ1, hQ2, hQ8, ?_, h11, ?_, ?_, ?_, hs2.1⟩ <;> try simp only [Tactic.rf]
    · rw [hs2.2, hs1.2]; exact hP2
    · rw [hs2.2, hs1.2]; exact hO2
    · rw [hs2.2, hs1.2]; exact hQ3
    · rw [x16]; omega
    · rw [x8]; omega
    · rw [x8']; omega
  · have hk0 : k = 0 := by
      have := congrArg BitVec.toNat hc_1; rw [x16] at this; omega
    have hle := BitVec.le_def.1 hc
    refine h190 _ _ ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, h18, h18, hn30, hle, .inr ⟨hQ1, hQ2, hQ8, ?_⟩, hs2.1⟩
    simp only [Tactic.rf]
    rw [hs2.2, hs1.2]; exact hQ3

set_option rv_sym.heap true in
/-- **From the label 73**: the placements' block (`alloc`), then the second loop, or none. -/
theorem at146 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {needA needH needS : Nat}
    (hal : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop))
    (hhe : Aborts env p L.handleError.idx needH) (hass : Aborts env p L.assertFailed.idx needS)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hnA : env.stackLimit.toNat + 112 + needA ≤ top.toNat) (hnH : env.stackLimit.toNat + 112 + needH ≤ top.toNat)
    (_hnS : env.stackLimit.toNat + 112 + needS ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (h190 : ∀ R M, Inv95 env m top ret regs R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 190, ret, top⟩ :: rest, R, M⟩)
    (hl2 : ∀ P O k R M, L2 env m top ret regs P O k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 170, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Inv73 env m top ret regs R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 146, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  obtain ⟨hR2, hR8, hR9, hsv, h18, hn30, hP, hM⟩ := hI
  have hlay := env.layout
  have := hW.nextAddr_ge
  have hW1 := hW.heapEnd_le
  have hge := hW.next_ge
  have hlim : env.stackLimit.toNat + 112 ≤ top.toNat := by omega
  obtain ⟨hsl, hF0, hS0, hc0⟩ := id hM
  have hnm := hF0.1
  have hnM := hF0.2.1
  have hs4 : (R .x18 <<< 4).toNat = 16 * (R .x18).toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hR := And.intro hR2 (And.intro hR8 (And.intro hR9 hsv))
  rv_introT hR
  rv_symT hp stop [170, 190] with [hL] using [hal, hhe, hass]
  · have hn0 : (regs .x14).toNat + (regs .x12).toNat = 0 := by rw [← h18, hc_1]; rfl
    refine h190 _ _ ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, h18, ?_, hn30, BitVec.le_def.1 hc, .inl hn0, hM⟩
    simp only [Tactic.rf]
    rw [hn0]; rfl
  · have hn0 : (R .x18).toNat ≠ 0 := fun h => hc_1 (BitVec.eq_of_toNat_eq h)
    obtain ⟨hP1, hP8, hP2, hO1, hO8, hO2⟩ := hP.resolve_left (by omega)
    have hM2 := memOk_call hlim hM hret2_14 hret2_15 hret2_19 fun a h => h.elim
    have hn2 := hret2_14.1
    have hE2 := hret2_14.2.1
    rw [hs4] at hret2_18
    have e8 : (r2 .x10 + 8#64).toNat = (r2 .x10).toNat + 8 := toNat_add_ofNat (by omega)
    have e8s : (r2 .x10 + 8#64 + R .x18 <<< 4).toNat = (r2 .x10).toNat + 8 + 16 * (R .x18).toNat := by
      rw [BitVec.toNat_add, e8, hs4]; omega
    refine hl2 (R .x19) (M.getMem (top + 18446744073709551512#64)) ((R .x18).toNat - 1) _ _
      ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, h18, hn30, by omega, hP1, hP8, by omega, hO1, hO8, by omega, ?_, ?_, hret2_17,
        ?_, ?_, ?_, ?_, ?_, hM2⟩ <;> simp only [Tactic.rf]
    · omega
    · omega
    · omega
    · rw [e8s]; omega
    · rw [e8]; omega
    · omega
    · omega

/-- The state at instruction 107 (label): the blocks' placements' block `T` (`x18`) of `nb` 16-byte elements (`x23`,
    `x24`; `x19` its bytes), allocated after the placements' `Q` (`x20`, capacity `x21`). -/
def Inv107 (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (R : Reg → Word) (M : MachineState) :
    Prop :=
  R .x2 = top + 18446744073709551504#64 ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧ Saved regs R ∧
    R .x23 = regs .x14 ∧ R .x24 = regs .x14 ∧ (R .x19).toNat = 16 * (regs .x14).toNat ∧
    (R .x21).toNat = (regs .x14).toNat + (regs .x12).toNat ∧ (regs .x14).toNat + (regs .x12).toNat < 2 ^ 30 ∧
    ((regs .x14).toNat + (regs .x12).toNat = 0 ∨ (0x10000000 ≤ (R .x20).toNat ∧ (env.next m).toNat ≤ (R .x20).toNat ∧
      (R .x20).toNat % 8 = 0 ∧ (R .x20).toNat + 16 * ((regs .x14).toNat + (regs .x12).toNat) ≤ (env.next M).toNat)) ∧
    ((regs .x14).toNat = 0 ∨ ((R .x20).toNat + 16 * ((regs .x14).toNat + (regs .x12).toNat) ≤ (R .x18).toNat ∧
      (env.next m).toNat ≤ (R .x18).toNat ∧ (R .x18).toNat % 8 = 0 ∧
      (R .x18).toNat + 16 * (regs .x14).toNat ≤ (env.next M).toNat)) ∧ (R .x18).toNat % 8 = 0 ∧
    MemOk env m top ret regs M

set_option rv_sym.heap true in
/-- **From the label 95**: the blocks' placements' block (`alloc`), or none. -/
theorem at190 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {needA needH : Nat}
    (hal : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop))
    (hhe : Aborts env p L.handleError.idx needH)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hnA : env.stackLimit.toNat + 112 + needA ≤ top.toNat) (hnH : env.stackLimit.toNat + 112 + needH ≤ top.toNat)
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (h214 : ∀ R M, Inv107 env m top ret regs R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 214, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Inv95 env m top ret regs R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 190, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  obtain ⟨hR2, hR8, hR9, hsv, h18, h21, hn30, hle, hQ, hM⟩ := hI
  have hlay := env.layout
  have := hW.nextAddr_ge
  have hW1 := hW.heapEnd_le
  have hge := hW.next_ge
  have hlim : env.stackLimit.toNat + 112 ≤ top.toNat := by omega
  obtain ⟨hsl, hF0, hS0, hc0⟩ := id hM
  have hnm := hF0.1
  have hnM := hF0.2.1
  have hsub : R .x18 - regs .x12 = regs .x14 := BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 (by omega))]; omega)
  have hs4 : (regs .x14 <<< 4).toNat = 16 * (regs .x14).toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hR := And.intro hR2 (And.intro hR8 (And.intro hR9 hsv))
  rv_introT hR
  rv_symT hp stop [214] with [hL] using [hal, hhe]
  · rw [hsub, hs4]; omega
  · rw [hsub, hs4] at hret1_18
    have hM1 := memOk_call hlim hM hret1_14 hret1_15 hret1_19 fun a h => h.elim
    have hn1 := hret1_14.1
    refine h214 _ _ ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, hsub, hsub, ?_, h21, hn30, ?_, ?_, hret1_17, hM1⟩ <;>
      simp only [Tactic.rf]
    · rw [hsub, hs4]
    · rcases hQ with h0 | ⟨h1, h2, h3, h4⟩
      · exact .inl h0
      · exact .inr ⟨h1, h2, h3, by omega⟩
    · rcases Nat.eq_zero_or_pos (regs .x14).toNat with h0 | h0
      · exact .inl h0
      · obtain ⟨h1, h2, h3, h4⟩ := hQ.resolve_left (by omega)
        exact .inr ⟨by omega, by omega, hret1_17, by omega⟩
  · have h0 : regs .x14 = 0#64 := by rw [← hsub, hc]; simp
    refine h214 _ _ ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, hsub, ?_, ?_, h21, hn30, hQ, .inl ?_, ?_, hM⟩ <;>
      try simp only [Tactic.rf]
    · rw [h0]
    · rw [hsub, hs4]
    · rw [h0]; rfl
    · rfl

/-- The state at instruction 113 (label), the blocks' placements copied: the two blocks `Q` (`x20`) and `T` (`x18`). -/
def Inv113 (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (R : Reg → Word) (M : MachineState) :
    Prop :=
  R .x2 = top + 18446744073709551504#64 ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧ Saved regs R ∧
    R .x23 = regs .x14 ∧ R .x24 = regs .x14 ∧
    (R .x21).toNat = (regs .x14).toNat + (regs .x12).toNat ∧ (regs .x14).toNat + (regs .x12).toNat < 2 ^ 30 ∧
    ((regs .x14).toNat + (regs .x12).toNat = 0 ∨ (0x10000000 ≤ (R .x20).toNat ∧ (env.next m).toNat ≤ (R .x20).toNat ∧
      (R .x20).toNat % 8 = 0 ∧ (R .x20).toNat + 16 * ((regs .x14).toNat + (regs .x12).toNat) ≤ (env.next M).toNat)) ∧
    ((regs .x14).toNat = 0 ∨ (0x10000000 ≤ (R .x18).toNat ∧ (env.next m).toNat ≤ (R .x18).toNat ∧
      (R .x18).toNat % 8 = 0 ∧ (R .x18).toNat + 16 * (regs .x14).toNat ≤ (env.next M).toNat)) ∧
    MemOk env m top ret regs M

set_option rv_sym.heap true in
/-- **From the label 107**: the blocks' placements copied into their block (`memcpy`). -/
theorem at214 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {needM : Nat} (hcp : MemcpySpecT env p L.memcpy.idx needM)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hnM : env.stackLimit.toNat + 112 + needM ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (h226 : ∀ R M, Inv113 env m top ret regs R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 226, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Inv107 env m top ret regs R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 214, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  obtain ⟨hR2, hR8, hR9, hsv, hR23, hR24, h19, h21, hn30, hQ, hT, hT8, hM⟩ := hI
  have hlay := env.layout
  have := hW.nextAddr_ge
  have hW1 := hW.heapEnd_le
  have hge := hW.next_ge
  have hlim : env.stackLimit.toNat + 112 ≤ top.toNat := by omega
  have e112 := Runtime.CloneT.toNat_add_neg (t := top) (c := 18446744073709551504#64) (k := 112) rfl (by omega)
  obtain ⟨hsl, hF0, hS0, hc0⟩ := id hM
  have hnm := hF0.1
  have hnM := hF0.2.1
  have hR := And.intro hR2 (And.intro hR8 (And.intro hR9 (And.intro hR23 (And.intro hR24 hsv))))
  rv_introT hR
  have hs4 : (regs .x12 <<< 4).toNat = 16 * (regs .x12).toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hsrc := (R .x20 + regs .x12 <<< 4).isLt
  have hQT : (regs .x14).toNat = 0 ∨ ((R .x20 + regs .x12 <<< 4).toNat = (R .x20).toNat + 16 * (regs .x12).toNat ∧
      0x10000000 ≤ (R .x20).toNat ∧ (R .x20).toNat + 16 * ((regs .x14).toNat + (regs .x12).toNat) ≤ (R .x18).toNat ∧
      (env.next m).toNat ≤ (R .x18).toNat ∧ (R .x18).toNat + 16 * (regs .x14).toNat ≤ (env.next M).toNat) := by
    rcases Nat.eq_zero_or_pos (regs .x14).toNat with h0 | h0
    · exact .inl h0
    · obtain ⟨h1, -, -, h4⟩ := hQ.resolve_left (by omega)
      obtain ⟨t1, t2, -, t4⟩ := hT.resolve_left (by omega)
      exact .inr ⟨by rw [BitVec.toNat_add, hs4]; omega, h1, t1, t2, t4⟩
  rv_symT hp stop [226] with [hL] using [hcp]
  · rcases hQT with h0 | ⟨e, q1, q2, q3, q4⟩
    · exact .inl (by omega)
    · refine .inr ⟨.inl ⟨by omega, by omega⟩, .inl (by omega), by rw [inWindow_iff, e]; omega, .inl ?_⟩
      show (R .x20 + regs .x12 <<< 4).toNat + _ ≤ _
      rw [e]; omega
  · have hM1 := memOk_call hlim hM hret1_14 hret1_15 hret1_19 fun b hb => .inl (by
      have := Runtime.VecHdrT.copyOut_in (P := R .x18) (by exact rfl) (by exact h19) hT8 hb
      have := hret1_14.1
      rcases hQT with h0 | ⟨-, -, -, q3, q4⟩
      · omega
      · omega)
    have hn1 := hret1_14.1
    refine h226 _ _ ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, rfl, rfl, h21, hn30, ?_, ?_, hM1⟩ <;> simp only [Tactic.rf]
    · rcases hQ with h0 | ⟨h1, h2, h3, h4⟩
      · exact .inl h0
      · exact .inr ⟨h1, h2, h3, by omega⟩
    · rcases hT with h0 | ⟨-, h2, h3, h4⟩
      · exact .inl h0
      · exact .inr ⟨by omega, h2, h3, by omega⟩

/-- **A vector's header at `a`** with capacity `c`, pointer `P` and length `l`: `VecT` of 16-byte elements. -/
theorem vecT_of {env : Env} {X : MachineState} {a c P l : Word} (hwin : InWin env a 24) (hal : a.toNat % 8 = 0)
    (h0 : X.getMem a = c) (h8 : X.getMem (a + 8#64) = P) (h16 : X.getMem (a + 16#64) = l)
    (hl : l.toNat ≤ c.toNat) (hn : c.toNat * 16 < 2 ^ 63)
    (hP : c.toNat = 0 ∨ (0x10000000 ≤ P.toNat ∧ P.toNat + c.toNat * 16 ≤ (env.next X).toNat ∧ P.toNat % 8 = 0)) :
    VecT env X a 16 ∧ vecLen X a = l ∧ vecPtr X a = P := by
  have hc : rvCapAt a = a := rvCapAt_eq _
  have hp : rvPtrAt a = a + 8#64 := rfl
  refine ⟨⟨hwin, ⟨Runtime.MemsetT.InWin.sub hwin (Nat.le_refl _) (by simp only [Layouts.RawVecInner.byteSize]; omega),
    hal, ?_, by rw [hc, h0]; exact hn⟩, by rw [vecLen_eq, vecCap_eq, h0, h16]; exact hl⟩, by rw [vecLen_eq, h16],
    by rw [vecPtr_eq, h8]⟩
  rw [hc, hp, h0, h8]
  rcases hP with h | ⟨h1, h3, h4⟩
  · exact .inl h
  · exact .inr ⟨h1, by unfold Env.Live; omega, h4⟩

/-- The result's seven stores at `h`, in the code's order. -/
abbrev res (M : MachineState) (h v32 v40 v48 v0 v8 v16 v24 : Word) : MachineState :=
  ((((((M.setMem (h + 32#64) v32).setMem (h + 40#64) v40).setMem (h + 48#64) v48).setMem h v0).setMem (h + 8#64)
    v8).setMem (h + 16#64) v16).setMem (h + 24#64) v24

/-- **The result's seven stores** at `h`, a caller's 56 bytes in a window: the slots, the frame with the result as its
    `out`, the static data, the code and `NEXT` kept; six of the words read back. -/
theorem res_ok {env : Env} {m M : MachineState} {top ret h v32 v40 v48 v0 v8 v16 v24 : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 112 ≤ top.toNat) (hh : regs .x10 = h) (hown : env.Owned m top h 56)
    (hwin : InWin env h 56) (hal : h.toNat % 8 = 0) (hM : MemOk env m top ret regs M) :
    let X := res M h v32 v40 v48 v0 v8 v16 v24
    Slots X top ret regs ∧ env.Frame top (Spec.Whir.SretOut 56 regs m) m X ∧ env.Static X ∧ X.code = m.code ∧
      env.next X = env.next M ∧ X.getMem h = v0 ∧ X.getMem (h + 8#64) = v8 ∧ X.getMem (h + 16#64) = v16 ∧
      X.getMem (h + 24#64) = v24 ∧ X.getMem (h + 32#64) = v32 ∧ X.getMem (h + 40#64) = v40 := by
  intro X
  obtain ⟨hsl, hF, hS, hc⟩ := hM
  have hlay := env.layout
  have h56 := hown.2
  have hnm := hF.1
  have hnM := hF.2.1
  have hwin' := hwin
  unfold InWin at hwin'
  have e : ∀ k, k ≤ 48 → (h + BitVec.ofNat 64 k).toNat = h.toNat + k := fun k hk => toNat_add_ofNat (by omega)
  have e8 := e 8 (by omega)
  have e16 := e 16 (by omega)
  have e24 := e 24 (by omega)
  have e32 := e 32 (by omega)
  have e40 := e 40 (by omega)
  have e48 := e 48 (by omega)
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  have hnx : ∀ k, k ≤ 48 → ∀ b : Word, b.toNat = h.toNat + k → b ≠ env.nextAddr := fun k hk b hb e => by
    rw [e] at hb; rcases hwin' with h1 | h1 <;> omega
  have hout : ∀ k, k ≤ 48 → ∀ b : Word, b.toNat = h.toNat + k → Spec.Whir.SretOut 56 regs m b :=
    fun k hk b hb => by show InRange (regs .x10) 56 b; unfold InRange; rw [hh]; omega
  have hst : ∀ k, k ≤ 48 → ∀ b : Word, b.toNat = h.toNat + k →
      b.toNat < env.staticLo.toNat ∨ env.staticHi.toNat ≤ b.toNat := fun k hk b hb => by
    rcases hwin' with h1 | h1 <;> omega
  have hsep : h.toNat + 56 ≤ top.toNat - 80 ∨ top.toNat ≤ h.toNat := by rcases hown.1 with h3 | h3 <;> omega
  refine ⟨slots_keep (by omega) (fun a h1 h2 => ?_) hsl, ?_, ?_, by simp only [X, MachineState.code_setMem]; exact hc,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [X]
    repeat rw [MachineState.getMem_setMem_ne (ne _ _ (by omega))]
  · simp only [X]
    exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out (Tactic.frame_out (Tactic.frame_out (Tactic.frame_out
      (Tactic.frame_out (Tactic.frame_weaken hF) (hout 32 (by omega) _ e32) (hnx 32 (by omega) _ e32))
      (hout 40 (by omega) _ e40) (hnx 40 (by omega) _ e40)) (hout 48 (by omega) _ e48) (hnx 48 (by omega) _ e48))
      (hout 0 (by omega) _ rfl) (hnx 0 (by omega) _ rfl)) (hout 8 (by omega) _ e8) (hnx 8 (by omega) _ e8))
      (hout 16 (by omega) _ e16) (hnx 16 (by omega) _ e16)) (hout 24 (by omega) _ e24) (hnx 24 (by omega) _ e24)
  · simp only [X]
    exact Tactic.static_store (Tactic.static_store (Tactic.static_store (Tactic.static_store (Tactic.static_store
      (Tactic.static_store (Tactic.static_store hS (hst 32 (by omega) _ e32)) (hst 40 (by omega) _ e40))
      (hst 48 (by omega) _ e48)) (hst 0 (by omega) _ rfl)) (hst 8 (by omega) _ e8)) (hst 16 (by omega) _ e16))
      (hst 24 (by omega) _ e24)
  · simp only [X]
    rw [Tactic.next_setMem (hnx 24 (by omega) _ e24), Tactic.next_setMem (hnx 16 (by omega) _ e16),
      Tactic.next_setMem (hnx 8 (by omega) _ e8), Tactic.next_setMem (hnx 0 (by omega) _ rfl),
      Tactic.next_setMem (hnx 48 (by omega) _ e48), Tactic.next_setMem (hnx 40 (by omega) _ e40),
      Tactic.next_setMem (hnx 32 (by omega) _ e32)]
  all_goals
    simp only [X]
    repeat (first | rw [MachineState.getMem_setMem_eq] | rw [MachineState.getMem_setMem_ne (ne _ _ (by omega))])

set_option rv_sym.heap true in
/-- **The return**, from the label 113: the result's seven words, the saved registers. -/
theorem fin {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) (Spec.Whir.SretOut 56) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hlim : env.stackLimit.toNat + 112 ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (h2 : regs .x2 = top) (hpre : PreT env regs m) :
    ∀ R M, Inv113 env m top ret regs R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 226, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  obtain ⟨hR2, hR8, hR9, hsv, hR23, hR24, h21, hn30, hQ, hT, hM⟩ := hI
  obtain ⟨hown, hwin, hal, -, -⟩ := hpre
  rw [h2] at hown
  have hlay := env.layout
  have := hW.nextAddr_ge
  have hW1 := hW.heapEnd_le
  have hge := hW.next_ge
  have hwin' := hwin
  unfold InWin at hwin'
  have h56 := hown.2
  have hnm := hM.2.1.1
  have hq : ∀ v : Word,
      env.Frame top (Spec.Whir.SretOut 56 regs m) m (res M (regs .x10) (R .x18) (regs .x14) v (R .x21) (R .x20) (regs .x12) (regs .x14)) ∧ env.Static (res M (regs .x10) (R .x18) (regs .x14) v (R .x21) (R .x20) (regs .x12) (regs .x14)) ∧
      BufT env (res M (regs .x10) (R .x18) (regs .x14) v (R .x21) (R .x20) (regs .x12) (regs .x14)) ((res M (regs .x10) (R .x18) (regs .x14) v (R .x21) (R .x20) (regs .x12) (regs .x14)).getMem (rvCapAt (regs .x10))) ((res M (regs .x10) (R .x18) (regs .x14) v (R .x21) (R .x20) (regs .x12) (regs .x14)).getMem (rvPtrAt (regs .x10))) 16 ∧
      ((res M (regs .x10) (R .x18) (regs .x14) v (R .x21) (R .x20) (regs .x12) (regs .x14)).getMem (rvCapAt (regs .x10))).toNat * 16 < 2 ^ 63 ∧
      ((regs .x12).toNat = 0 ∨ env.Fresh m (res M (regs .x10) (R .x18) (regs .x14) v (R .x21) (R .x20) (regs .x12) (regs .x14)) (R .x20) ((regs .x12).toNat * 16)) ∧
      BufT env (res M (regs .x10) (R .x18) (regs .x14) v (R .x21) (R .x20) (regs .x12) (regs .x14)) ((res M (regs .x10) (R .x18) (regs .x14) v (R .x21) (R .x20) (regs .x12) (regs .x14)).getMem (rvCapAt (regs .x10 + 24#64))) ((res M (regs .x10) (R .x18) (regs .x14) v (R .x21) (R .x20) (regs .x12) (regs .x14)).getMem (rvPtrAt (regs .x10 + 24#64))) 16 ∧
      ((res M (regs .x10) (R .x18) (regs .x14) v (R .x21) (R .x20) (regs .x12) (regs .x14)).getMem (rvCapAt (regs .x10 + 24#64))).toNat * 16 < 2 ^ 63 ∧
      ((regs .x14).toNat = 0 ∨ env.Fresh m (res M (regs .x10) (R .x18) (regs .x14) v (R .x21) (R .x20) (regs .x12) (regs .x14)) (R .x18) ((regs .x14).toNat * 16)) := fun v => by
    obtain ⟨-, f, t, -, n, r0, r8, r16, r24, r32, r40⟩ := res_ok (v32 := R .x18) (v40 := regs .x14) (v48 := v)
      (v0 := R .x21) (v8 := R .x20) (v16 := regs .x12) (v24 := regs .x14) hlim rfl hown hwin hal hM
    have p32 : regs .x10 + 24#64 + 8#64 = regs .x10 + 32#64 := by rw [BitVec.add_assoc]; rfl
    have p40 : regs .x10 + 24#64 + 16#64 = regs .x10 + 40#64 := by rw [BitVec.add_assoc]; rfl
    have e24 : (regs .x10 + 24#64).toNat = (regs .x10).toNat + 24 := toNat_add_ofNat (by omega)
    obtain ⟨v1, l1, q1⟩ := vecT_of (env := env) (Runtime.MemsetT.InWin.sub hwin (Nat.le_refl _) (by omega)) hal r0 r8 r16
      (by omega) (by omega) (by
        rcases hQ with h0 | ⟨h1, -, h3, h4⟩
        · exact .inl (by omega)
        · exact .inr ⟨h1, by rw [n]; omega, h3⟩)
    obtain ⟨v2, l2, q2⟩ := vecT_of (env := env) (c := regs .x14) (P := R .x18) (l := regs .x14)
      (Runtime.MemsetT.InWin.sub hwin (by omega) (by omega)) (by omega) r24 (by rw [p32, r32]) (by rw [p40, r40])
      (Nat.le_refl _) (by omega) (by
        rcases hT with h0 | ⟨h1, -, h3, h4⟩
        · exact .inl h0
        · exact .inr ⟨h1, by rw [n]; omega, h3⟩)
    refine ⟨f, t, v1.2.1.2.2.1, v1.2.1.2.2.2, ?_, v2.2.1.2.2.1, v2.2.1.2.2.2, ?_⟩
    · rcases Nat.eq_zero_or_pos (regs .x12).toNat with h0 | h0
      · exact .inl h0
      · obtain ⟨-, h2, -, h4⟩ := hQ.resolve_left (by omega)
        exact .inr ⟨h2, by rw [n]; omega⟩
    · rcases hT with h0 | ⟨-, h2, -, h4⟩
      · exact .inl h0
      · exact .inr ⟨h2, by rw [n]; omega⟩
  have hR := And.intro hR2 (And.intro hR8 (And.intro hR9 (And.intro hR23 (And.intro hR24 hsv))))
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10⟩ := hM.1
  have hc0 := hM.2.2.2
  have hsep : (regs .x10).toNat + 56 ≤ top.toNat - 80 ∨ top.toNat ≤ (regs .x10).toNat := by
    have := hM.2.1.2.1
    rcases hown.1 with h3 | h3 <;> omega
  clear hM hQ hT
  rv_introT hR
  rv_symT hp with [_hL]
  · exact (hq (R .x22)).1
  · exact (hq (R .x22)).2.1
  · exact (hq (R .x22)).2.2.1
  · exact (hq (R .x22)).2.2.2.1
  · exact (hq (R .x22)).2.2.2.2.1
  · exact (hq (R .x22)).2.2.2.2.2.1
  · exact (hq (R .x22)).2.2.2.2.2.2.1
  · exact (hq (R .x22)).2.2.2.2.2.2.2

set_option rv_sym.heap true in
/-- **`bus_layout` is total**, with 112 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA needH needR needM needO needS : Nat} (hnH : 112 + needH ≤ need) (hnA : 112 + needA ≤ need)
    (hnR : 112 + needR ≤ need) (hnM : 112 + needM ≤ need) (hcp : MemcpySpecT env p L.memcpy.idx needM)
    (hnS : 112 + needS ≤ need) (hass : Aborts env p L.assertFailed.idx needS)
    (hnO : 112 + needO ≤ need) (hso : Multilinear.StackOffsetsT.SpecT env p L.stackOffsets.idx needO)
    (hhe : Aborts env p L.handleError.idx needH) (hal : AllocSpecT env p L.alloc.idx needA)
    (hre : ReserveSpecT env 8 8 p L.reserve.idx needR) :
    SpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp stop [54] with [hL] using [hhe, hal']
  all_goals
    have hlay := env.layout
    have hlim : env.stackLimit.toNat + 112 ≤ top.toNat := by omega
    have := hpre_13.nextAddr_ge
    have hW1 := hpre_13.heapEnd_le
    have hge := hpre_13.next_ge
    have htop := hpre_13.top_le
    have hM0 := saved_ok (ret := ret) (regs := regs) hlim hpre_5 hpre_4
    simp only [saved] at hM0
    have hnf : (regs .x12).toNat * 8 < 2 ^ 32 := by
      rcases hpre_10 with h | ⟨h1, -, -⟩
      · omega
      · rw [inWindow_iff] at h1; omega
    have hnb : (regs .x14).toNat * 48 < 2 ^ 32 := by
      rcases hpre_11 with h | ⟨-, h2, -⟩
      · omega
      · unfold Env.Live at h2; omega
    have hn : (regs .x14 + regs .x12).toNat = (regs .x14).toNat + (regs .x12).toNat := by
      rw [BitVec.toNat_add]; omega
    have hsh : ((regs .x14 + regs .x12) <<< 3).toNat = 8 * (regs .x14 + regs .x12).toNat := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
    have hpre : PreT env regs m := ⟨⟨hpre_6, hpre_7⟩, hpre_8, hpre_9, hpre_10, hpre_11⟩
    have h226 := fin hp hL hk hlim hpre_13 hpre_12 hpre_2 hpre
    have h214 := at214 hp hL hcp (by omega) hpre_13 hpre_12 h226
    have h190 := at190 hp hL hal' hhe hstop (by omega) (by omega) hpre_13 hpre_12 h214
    have h146 := at146 hp hL hal' hhe hass hstop (by omega) (by omega) (by omega) hpre_13 hpre_12 h190
      fun P O k R M h => loop2 hp hL hass hstop (by omega) hpre_13 hpre_12 h190 k R M h
    have h118 := at118 hp hL hso hhe hstop (by omega) (by omega) hpre_13 hpre_12 h146
    have h90 := at90 hp hL hpre_13 hpre_11 h118 (loop1 hp hL hlim hpre_13 hpre_12 h118)
    have h74 := at74 hp hL hcp (by omega) hpre_13 hpre_12 hpre_2 hpre_10 h90
    have h54 := at54 hp hL hre hstop (by omega) hpre_13 hpre_12 h74
  · refine h54 _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ⟨rfl, rfl, rfl⟩, hn, ?_, .inl ?_, hM0⟩ <;>
      simp only [Tactic.rf]
    · rw [hc]
    · omega
    · rw [hc]; rfl
  · rw [hsh]; omega
  · have hM1 := memOk_call hlim hM0 hret1_14 hret1_15 hret1_19 fun a h => h.elim
    rw [hsh] at hret1_18
    refine h54 _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, hn, ?_, .inr ⟨?_, hret1_16, hret1_17, ?_⟩,
      hM1⟩ <;> simp only [Tactic.rf] <;> omega

end Rv64mc.Proof.Bus.BusLayoutT

/-- info: 'Rv64mc.Proof.Bus.BusLayoutT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Bus.BusLayoutT.total
