/-
  Rv64mc.Proof.Whir.SampleQueriesT

  `verifier::whir::sample_queries(transcript, block_length, count)` is total (`specT`): from a transcript
  `TranscriptAtT` (`TranscriptReprT`) owned with its proof (`OwnedT`), and a result's slot of `24` bytes owned, in a
  window, 8-byte aligned, apart from both (`NextScalarT.PreT`), it returns with the transcript `TranscriptAtT` and
  owned again, its proof's address kept, and, unless the slot holds `Err` (its first word the niche `-1`), the
  queries at the slot a vector of words (`VecReprT.VecT`) of `count` elements, writing at most the slot, the sponge
  and the stream offset besides what it allocates (`TOut`, the partial contract's), or the run ends with `a0 = 2`
  where `alloc`, `Sponge::sample` or the allocation's `handle_error` does. Safety only: the partial contract's
  queries (`Spec/Whir/Transcript.lean`'s `sampleQueriesSpec`, `Model.sampleQueriesRust`) are `Sponge::sample`'s
  functional ones. It has no partial proof (class C). `log2_strict`'s two constant tables are an environment fact
  (`DataRef.InData env (tables L)`), as `MerkleT`'s.

  The vector is allocated with capacity `count`, so `RawVec<u64>::grow_one` is never reached: its call is refuted
  (the length is below the count, which is the capacity), not stepped. Cut at `Sponge::sample`'s call (instruction
  152, `call_ok`, `CInv`), at the inner loop's head (instruction 194, `loop`: `Total.loop` with the elements left as
  the measure; every pass of either loop pushes one) and at the exit (instruction 234, `fin_ok`, `FinInv`). The
  memory facts the parts keep (`BaseM`) are carried across each call and store by a lemma (`baseM_sample`,
  `baseM_callF`, `baseM_store`).

  ## Main definitions

  * `PreT`, `OkVec`, `PostT`, `specT`, `PostK`, `tables`, `Saved`, `BaseM`, `Mem`, `LInv`, `CInv`, `FinInv`

  ## Main results

  * `fin_ok`, `call_ok`, `loop`, `kept`, `total`
-/

import Rv64mc.Proof.Transcript.NextScalarsT
import Rv64mc.Proof.Transcript.SampleT
import Rv64mc.Proof.Transcript.MerkleT
import Rv64mc.Proof.Runtime.AllocT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Spec.Whir.Transcript
import Rv64mc.Gen.Tmpl.Verifier.Whir.SampleQueries

namespace Rv64mc.Proof.Whir.SampleQueriesT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Transcript Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT RawVecT BufT)
open Rv64mc.Proof.Transcript
open Rv64mc.Proof.Transcript.SpongeReprT Rv64mc.Proof.Transcript.TranscriptReprT
open Rv64mc.Proof.Transcript.NextScalarsT (Ctx sret_spongeT tr_words)
open Rv64mc.Gen.Verifier.Whir.SampleQueries (Link tmpl)

/-- The total precondition: `next_scalar`'s (`NextScalarT.PreT`): the transcript `TranscriptAtT` and owned with its
    proof, the result's slot (`24` bytes) owned, in a window, 8-byte aligned, apart from both. -/
abbrev PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  NextScalarT.PreT env regs m

/-- Unless the slot holds `Err`, the slot a vector of words of `count` (`a3`) elements. -/
def OkVec (env : Env) (regs : Reg → Word) (m' : MachineState) : Prop :=
  m'.getMem (regs .x10) ≠ 18446744073709551615#64 → VecT env m' (regs .x10) 8 ∧ vecLen m' (regs .x10) = regs .x13

/-- The total postcondition: the transcript `TranscriptAtT` and owned again, its proof's address kept, `OkVec`. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  TranscriptAtT env m' (regs .x11) ∧ OwnedT env m' (regs .x2) (regs .x11) ∧
    m'.getMem (regs .x11 + 328#64) = m.getMem (regs .x11 + 328#64) ∧ OkVec env regs m'

/-- **The total contract of `sample_queries`**: `PreT` to `PostT`, writing at most the slot, the sponge and the
    stream offset (`TOut`, the partial contract's), or ending the run with `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) (Spec.Whir.Transcript.TOut Layouts.ResultVecU64.byteSize)
    (Stop := AbortStop)

/-- What the run gives, from which `PostT` follows with the frame: the sponge `SpongeT`, `OkVec`. -/
def PostK (env : Env) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  SpongeT env m' (regs .x11) ∧ OkVec env regs m'

/-- The two constant tables `log2_strict` reads (the de Bruijn multiplier and its 64-byte index). -/
abbrev tables (L : Link) : List (DataRef × List Word) :=
  [(L.d_c8_14ca7de5, Gen.Verifier.Whir.SampleQueries.d_c8_14ca7de5_words),
    (L.d_c64_b1d69b10, Gen.Verifier.Whir.SampleQueries.d_c64_b1d69b10_words)]

/-- The saved registers' thirteen slots. -/
def Saved (ret top : Word) (regs : Reg → Word) (M : MachineState) : Prop :=
  M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551560#64) = regs .x21 ∧ M.getMem (top + 18446744073709551552#64) = regs .x22 ∧
    M.getMem (top + 18446744073709551544#64) = regs .x23 ∧ M.getMem (top + 18446744073709551536#64) = regs .x24 ∧
    M.getMem (top + 18446744073709551528#64) = regs .x25 ∧ M.getMem (top + 18446744073709551520#64) = regs .x26 ∧
    M.getMem (top + 18446744073709551512#64) = regs .x27

/-- What every part keeps of the memory: the frame, the code, the static data, the saved registers' slots, the
    transcript `TranscriptAtT` and owned, its proof's address. -/
def BaseM (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (M : MachineState) : Prop :=
  env.Frame top (NextScalar.Out 24 regs m) m M ∧ M.code = m.code ∧ env.Static M ∧ Saved ret top regs M ∧
    TranscriptAtT env M (regs .x11) ∧ OwnedT env M top (regs .x11) ∧
    M.getMem (regs .x11 + 328#64) = m.getMem (regs .x11 + 328#64)

/-- The frame's words in the loop: the slot's address (`sp + 8`), the transcript (`sp + 0x10`), the count
    (`sp + 0x18`), the vector's capacity the count (`sp + 0x20`), its buffer `BufT`, allocated since the entry
    (`sp + 0x28`), of fewer than `2^63` bytes. -/
def Mem (env : Env) (top : Word) (regs : Reg → Word) (m : MachineState) (M : MachineState) : Prop :=
  M.getMem (top + 18446744073709551464#64) = regs .x10 ∧ M.getMem (top + 18446744073709551472#64) = regs .x11 ∧
    M.getMem (top + 18446744073709551480#64) = regs .x13 ∧ M.getMem (top + 18446744073709551488#64) = regs .x13 ∧
    BufT env M (regs .x13) (M.getMem (top + 18446744073709551496#64)) 8 ∧ (regs .x13).toNat * 8 < 2 ^ 63 ∧
    (env.next m).toNat ≤ (M.getMem (top + 18446744073709551496#64)).toNat

/-- The inner loop's head (instruction 194), `k` elements left: the stack pointer, the buffer in `x19`, the length in
    `x23` and stored (`sp + 0x30`), `x27` its offset, the count in `x26`. -/
def LInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551456#64 ∧ R .x19 = M.getMem (top + 18446744073709551496#64) ∧ R .x26 = regs .x13 ∧
    M.getMem (top + 18446744073709551504#64) = R .x23 ∧ (R .x27).toNat = 8 * (R .x23).toNat ∧
    (R .x23).toNat + k = (regs .x13).toNat ∧ Mem env top regs m M ∧ BaseM env ret top regs m M

/-- `Sponge::sample`'s call (instruction 152), `k` elements left, at least one: the transcript in `x10`, the count
    in `x18`, the rest as `LInv`. -/
def CInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551456#64 ∧ R .x10 = regs .x11 ∧ R .x18 = regs .x13 ∧
    R .x19 = M.getMem (top + 18446744073709551496#64) ∧ M.getMem (top + 18446744073709551504#64) = R .x23 ∧
    (R .x23).toNat + k = (regs .x13).toNat ∧ 1 ≤ k ∧ Mem env top regs m M ∧ BaseM env ret top regs m M

/-- The exit (instruction 234): the vector's header (`sp + 0x20`) with its buffer `BufT`, of fewer than `2^63`
    bytes, its length the count, within its capacity; the slot's address at `sp + 8`. -/
def FinInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551456#64 ∧ M.getMem (top + 18446744073709551464#64) = regs .x10 ∧
    BufT env M (M.getMem (top + 18446744073709551488#64)) (M.getMem (top + 18446744073709551496#64)) 8 ∧
    (M.getMem (top + 18446744073709551488#64)).toNat * 8 < 2 ^ 63 ∧
    M.getMem (top + 18446744073709551504#64) = regs .x13 ∧
    (regs .x13).toNat ≤ (M.getMem (top + 18446744073709551488#64)).toNat ∧ BaseM env ret top regs m M

set_option hygiene false in
/-- A word `top + c` of the frame, as a number. -/
local macro "tn" : tactic => `(tactic| (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))

/-- The saved registers' slots, in a memory that keeps the words `top - c` for `8 ≤ c ≤ 104`. -/
theorem Saved.keep {ret top : Word} {regs : Reg → Word} {M M' : MachineState} (h : Saved ret top regs M)
    (e : ∀ c : Nat, 8 ≤ c → c ≤ 104 → M'.getMem (top + BitVec.ofNat 64 (2 ^ 64 - c)) =
      M.getMem (top + BitVec.ofNat 64 (2 ^ 64 - c))) : Saved ret top regs M' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨(e 8 (by omega) (by omega)).trans h1, (e 16 (by omega) (by omega)).trans h2,
    (e 24 (by omega) (by omega)).trans h3, (e 32 (by omega) (by omega)).trans h4,
    (e 40 (by omega) (by omega)).trans h5, (e 48 (by omega) (by omega)).trans h6,
    (e 56 (by omega) (by omega)).trans h7, (e 64 (by omega) (by omega)).trans h8,
    (e 72 (by omega) (by omega)).trans h9, (e 80 (by omega) (by omega)).trans h10,
    (e 88 (by omega) (by omega)).trans h11, (e 96 (by omega) (by omega)).trans h12,
    (e 104 (by omega) (by omega)).trans h13⟩

/-- **`BaseM` after a store** to a word not the saved registers' nor the transcript's: in the frame below the
    saved registers' slots, or allocated since the entry. -/
theorem baseM_store {env : Env} {ret top : Word} {regs : Reg → Word} {m M : MachineState} {a v : Word}
    (hB : BaseM env ret top regs m M) (hO0 : OwnedT env m top (regs .x11))
    (hlim : env.stackLimit.toNat + 160 ≤ top.toNat)
    (ha : (top.toNat - 160 ≤ a.toNat ∧ a.toNat + 8 ≤ top.toNat - 104) ∨
      ((env.next m).toNat ≤ a.toNat ∧ a.toNat + 8 ≤ (env.next M).toNat)) :
    BaseM env ret top regs m (M.setMem a v) := by
  obtain ⟨hF, hcM, hs, hSv, hT, hO, hP⟩ := hB
  have hlay := env.layout
  have hnM := hF.2.1
  have hnM' := hF.1
  have hna : a ≠ env.nextAddr := Tactic.ne_of_toNat (by omega)
  have hw := tr_words hO0 hP (a := a) (by omega)
  have hq : (M.setMem a v).getMem (regs .x11 + 328#64) = M.getMem (regs .x11 + 328#64) :=
    MachineState.getMem_setMem_ne hw.2.2.1
  refine ⟨?_, by rw [MachineState.code_setMem]; exact hcM, Tactic.static_store hs (by omega),
    hSv.keep fun c hc0 hc1 => MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by tn)),
    hT.of_get (MachineState.getMem_setMem_ne hw.1) (MachineState.getMem_setMem_ne hw.2.1) hq
      (MachineState.getMem_setMem_ne hw.2.2.2.1) (MachineState.getMem_setMem_ne hw.2.2.2.2),
    OwnedT.of_next hO (by rw [Tactic.next_setMem hna]) hq, hq.trans hP⟩
  rcases ha with ha | ha
  · exact Tactic.frame_slot hF (by omega) (by omega)
  · exact Tactic.frame_fresh hF rfl ha.1 (by omega)

/-- **`BaseM` across a call that writes nothing outside its stack and its allocations**, from a stack top below
    the frame. -/
theorem baseM_callF {env : Env} {ret top top' : Word} {regs : Reg → Word} {m M m1 : MachineState}
    (hB : BaseM env ret top regs m M) (hlim : env.stackLimit.toNat ≤ top'.toNat)
    (htop : top'.toNat + 104 ≤ top.toNat) (hf : env.Frame top' Tactic.F M m1) (hc : m1.code = M.code)
    (hs : env.Static m1) : BaseM env ret top regs m m1 := by
  obtain ⟨hF, hcM, -, hSv, hT, hO, hP⟩ := hB
  have hlay := env.layout
  have hnM := hF.2.1
  have hf' : env.Frame top Tactic.F M m1 := Env.Frame.trans (Env.Frame.refl hnM) hf (by omega) fun _ h => h.elim
  have hTT := hT.frameF hO hf' hnM (by omega)
  refine ⟨Env.Frame.trans hF hf (by omega) fun _ h => h.elim, hc.trans hcM, hs,
    hSv.keep fun c hc0 hc1 => hf.getMem_above (by omega) (by tn) id, hTT.1, hTT.2.1, hTT.2.2.trans hP⟩

/-- A word at or above `Sponge::sample`'s stack top and apart from the sponge, an object the caller owns, is kept
    by it. -/
theorem sample_keep {env : Env} {top' a T : Word} {r : Reg → Word} {M m1 : MachineState}
    (hf : env.Frame top' (Sample.Out r M) M m1) (hlim : env.stackLimit.toNat ≤ top'.toNat)
    (ha : top'.toNat ≤ a.toNat) (hT : r .x10 = T) (hap : a.toNat + 8 ≤ T.toNat ∨ T.toNat + 328 ≤ a.toNat) :
    m1.getMem a = M.getMem a :=
  hf.getMem_above hlim ha fun h => by
    simp only [Sample.Out, InRange, hT, Layouts.Sponge.byteSize] at h; omega

/-- **`BaseM` across `Sponge::sample`** on the transcript's sponge, which it leaves `SpongeT`, from a stack top
    below the frame. -/
theorem baseM_sample {env : Env} {ret top top' : Word} {regs r : Reg → Word} {m M m1 : MachineState}
    (hB : BaseM env ret top regs m M) (hlim : env.stackLimit.toNat ≤ top'.toNat)
    (htop : top'.toNat + 104 ≤ top.toNat) (hT : r .x10 = regs .x11)
    (hf : env.Frame top' (Sample.Out r M) M m1) (hc : m1.code = M.code) (hs : env.Static m1)
    (hS : SpongeT env m1 (regs .x11)) : BaseM env ret top regs m m1 := by
  obtain ⟨hF, hcM, -, hSv, hTr, hO, hP⟩ := hB
  have hlay := env.layout
  have hnM := hF.2.1
  obtain ⟨hO1, hO2⟩ := hO.1
  simp only [Layouts.Transcript.byteSize] at hO1 hO2
  have hap := hTr.2.2.1
  have hqw := hTr.2.2.2.2.1.lt
  simp only [Layouts.Proof.byteSize] at hqw
  unfold Apart at hap
  simp only [Layouts.Transcript.byteSize, Layouts.Proof.byteSize] at hap
  have hf' : env.Frame top (Sample.Out r M) M m1 := Env.Frame.trans (Env.Frame.refl hnM) hf (by omega)
    fun a h => Or.inr (Or.inr (Or.inr h))
  have hTT := hTr.frameS hS hO hf' hnM (by omega)
    (by simp only [Sample.Out, InRange, hT, Layouts.Sponge.byteSize]; rw [toNat_add_ofNat (by omega)]; omega)
    (fun k hk => by
      simp only [Sample.Out, InRange, hT, Layouts.Sponge.byteSize]
      rw [toNat_add_ofNat (by rcases hk with rfl | rfl <;> omega)]; rcases hk with rfl | rfl <;> omega)
  refine ⟨Env.Frame.trans hF hf (by omega) fun a h => ?_, hc.trans hcM, hs,
    hSv.keep fun c hc0 hc1 => sample_keep hf (by omega) (by tn) hT (by tn), hTT.1, hTT.2.1, hTT.2.2.trans hP⟩
  simp only [Sample.Out, hT] at h
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

/-- **A `Vec` header stored into a slot** in a window, 8-byte aligned, from a buffer `BufT` of words. -/
theorem vecT_stores {env : Env} {M : MachineState} {a c q l : Word} (hw : InWin env a 24) (ha : a.toNat % 8 = 0)
    (hb : BufT env M c q 8) (hc : c.toNat * 8 < 2 ^ 63) (hl : l.toNat ≤ c.toNat) :
    VecT env (((M.setMem a c).setMem (a + 8#64) q).setMem (a + 16#64) l) a 8 ∧
      vecLen (((M.setMem a c).setMem (a + 8#64) q).setMem (a + 16#64) l) a = l := by
  have hlt := hw.lt
  have e8 : (a + 8#64).toNat = a.toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (a + 16#64).toNat = a.toNat + 16 := toNat_add_ofNat (by omega)
  have n1 : a ≠ a + 16#64 := Tactic.ne_of_toNat (by rw [e16]; omega)
  have n2 : a ≠ a + 8#64 := Tactic.ne_of_toNat (by rw [e8]; omega)
  have n3 : a + 8#64 ≠ a + 16#64 := Tactic.ne_of_toNat (by rw [e8, e16]; omega)
  have hna : ∀ x : Word, x.toNat = a.toNat ∨ x.toNat = a.toNat + 8 ∨ x.toNat = a.toNat + 16 → x ≠ env.nextAddr :=
    fun x hx => hw.ne_next (by omega) (by omega)
  have hn : env.next (((M.setMem a c).setMem (a + 8#64) q).setMem (a + 16#64) l) = env.next M := by
    rw [Tactic.next_setMem (hna _ (by omega)), Tactic.next_setMem (hna _ (by omega)),
      Tactic.next_setMem (hna _ (by omega))]
  have r0 : (((M.setMem a c).setMem (a + 8#64) q).setMem (a + 16#64) l).getMem (a + BitVec.ofNat 64 0) = c := by
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero, MachineState.getMem_setMem_ne n1,
      MachineState.getMem_setMem_ne n2, MachineState.getMem_setMem_eq]
  have r8 : (((M.setMem a c).setMem (a + 8#64) q).setMem (a + 16#64) l).getMem (a + BitVec.ofNat 64 8) = q := by
    rw [show BitVec.ofNat 64 8 = 8#64 from rfl, MachineState.getMem_setMem_ne n3, MachineState.getMem_setMem_eq]
  have r16 : (((M.setMem a c).setMem (a + 8#64) q).setMem (a + 16#64) l).getMem (a + BitVec.ofNat 64 16) = l := by
    rw [show BitVec.ofNat 64 16 = 16#64 from rfl, MachineState.getMem_setMem_eq]
  refine ⟨⟨hw, ⟨hw.sub (Nat.le_refl _) (by simp only [Layouts.RawVecInner.byteSize]; omega), ha, ?_, ?_⟩, ?_⟩, ?_⟩
  · simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, r0, r8]
    exact hb.mono (by rw [hn])
  · simp only [rvCapAt, Layouts.RawVecInner.cap, r0]; exact hc
  · simp only [vecCap, vecLen, Layouts.Vec.cap, Layouts.Vec.len, r0, r16]; exact hl
  · simp only [vecLen, Layouts.Vec.len, r16]

/-- The capacity's overflow check passed: `count` words fit in `2^63` bytes. -/
theorem ovf {x : Word}
    (h : BinOp.ult.eval 0#64 (x >>> 61) ||| BinOp.ult.eval 9223372036854775800#64 (x <<< 3) = 0#64) :
    x.toNat * 8 < 2 ^ 63 := by
  simp only [BinOp.eval] at h
  refine Nat.lt_of_not_le fun hx => ?_
  rcases Nat.lt_or_ge x.toNat (2 ^ 61) with h1 | h1
  · have e : (9223372036854775800#64).ult (x <<< 3) = true := by
      simp only [BitVec.ult, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, decide_eq_true_eq]
      rw [Nat.mod_eq_of_lt (by omega)]; simp; omega
    simp [e] at h
  · have e : (0#64).ult (x >>> 61) = true := by
      simp only [BitVec.ult, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, decide_eq_true_eq]
      simp; omega
    simp [e] at h

/-- Two words stored into the slot, at `0` and `8`, apart from the transcript, keep its sponge `SpongeT`. -/
theorem spongeT_err {env : Env} {M : MachineState} {a T v w : Word} (hw : InWin env a 24)
    (hT : SpongeT env M T) (hap : Apart a 24 T Layouts.Transcript.byteSize) (hlT : T.toNat + 360 < 2 ^ 64) :
    SpongeT env ((M.setMem a v).setMem (a + 8#64) w) T := by
  have hlt := hw.lt
  unfold Apart at hap
  simp only [Layouts.Transcript.byteSize] at hap
  have e8 : (a + 8#64).toNat = a.toNat + 8 := toNat_add_ofNat (by omega)
  have e320 : (T + 320#64).toNat = T.toNat + 320 := toNat_add_ofNat (by omega)
  refine spongeT_of_get hT ?_ ?_
  · rw [MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by rw [e8]; omega)),
      MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega))]
  · rw [MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by rw [e8, e320]; omega)),
      MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by rw [e320]; omega))]

/-- A word of the frame, read through two stores into a slot the caller owns, at `0` and `8`. -/
theorem rd_slot2 {env : Env} {m M : MachineState} {top a x v w : Word} (ho : env.Owned m top a 24)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hlim : env.stackLimit.toNat ≤ x.toNat)
    (hx : x.toNat + 8 ≤ top.toNat) : ((M.setMem a v).setMem (a + 8#64) w).getMem x = M.getMem x := by
  have := env.layout
  have h2 := ho.2
  have e8 : (a + 8#64).toNat = a.toNat + 8 := toNat_add_ofNat (by omega)
  rcases ho.1 with h | h <;>
    rw [MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by rw [e8]; omega)),
      MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega))]

/-- `8 x` as the code computes it. -/
theorem shl3 {x : Word} (h : 8 * x.toNat < 2 ^ 64) : (x <<< 3).toNat = 8 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

set_option rv_sym.heap true in
/-- **The exit**: the vector's header copied into the slot as `Ok`, the epilogue, the return. -/
theorem fin_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostK env) (NextScalar.Out 24) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 160 ≤ need)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hC : Ctx env top regs m) :
    ∀ R M, FinInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 234, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  obtain ⟨-, -, hbuf, hcap, hlen, hlc, hBM⟩ := id hinv
  rv_introT hinv
  have hwS := hC.wS
  have haS := hC.aS
  have hoS := hC.oS
  rv_symT hp with [(by omega : env.stackLimit.toNat + 160 ≤ top.toNat)]
  all_goals
    simp only [hinv_2]
    have hlS := hwS.lt
    have hlT := hC.tT.2.1.lt
    have hsT : SpongeT env M (regs .x11) := ⟨hinv_23, hinv_24, hinv_25, hinv_26⟩
    have o : ∀ k : Nat, k < 24 → NextScalar.Out 24 regs m (regs .x10 + BitVec.ofNat 64 k) := fun k hk =>
      Or.inl ⟨by rw [toNat_add_ofNat (by omega)]; omega, by rw [toNat_add_ofNat (by omega)]; omega⟩
    have n : ∀ k : Nat, k < 24 → regs .x10 + BitVec.ofNat 64 k ≠ env.nextAddr := fun k hk => hwS.ne_next_add hk
    have o0 : NextScalar.Out 24 regs m (regs .x10) := Or.inl ⟨Nat.le_refl _, by omega⟩
    have n0 : regs .x10 ≠ env.nextAddr := hwS.ne_next (Nat.le_refl _) (by omega)
  · exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out hinv_7 o0 n0) (o 8 (by omega)) (n 8 (by omega)))
      (o 16 (by omega)) (n 16 (by omega))
  · exact (sret_spongeT hwS hsT hC.apST hlT).2.2.1
  · exact (sret_spongeT hwS hsT hC.apST hlT).2.2.2
  · intro _
    have h := vecT_stores (l := M.getMem (top + 18446744073709551504#64)) hwS haS hinv_3 hinv_4
      (by rw [hinv_5]; exact hinv_6)
    exact ⟨h.1, h.2.trans hinv_5⟩

set_option rv_sym.heap true in
/-- **`Sponge::sample`'s call**, on to the inner loop's head. -/
theorem call_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needS : Nat} (hnS : 160 + needS ≤ need) (hsa : SampleT.specT env p L.sample.idx needS)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    {k : Nat}
    (hnext : ∀ R M, LInv env ret top regs m k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 194, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, CInv env ret top regs m k R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 152, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  obtain ⟨-, -, -, -, h112, hlk, -, ⟨m152, m144, m136, m128, mb, mc, mn⟩, hBM⟩ := id hinv
  rv_introT hinv
  rv_symT hp stop [194] with [hL, (by omega : env.stackLimit.toNat + 160 ≤ top.toNat)] using [hsa]
  · exfalso; have := BitVec.lt_def.1 hc; omega
  · have hlay := env.layout
    have hnM := hBM.1.2.1
    have hO := hinv_40
    simp only [Layouts.Transcript.byteSize] at hO
    have e : ∀ a : Word, top.toNat - 160 ≤ a.toNat → a.toNat + 8 ≤ top.toNat → m1.getMem a = M.getMem a :=
      fun a h0 h1 => sample_keep (T := regs .x11) hret1_14 (by tn) (by tn)
        (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]) (by omega)
    have e120 := e (top + 18446744073709551496#64) (by tn) (by tn)
    refine hnext _ _ ⟨by rv_closeT, ?_, by rv_closeT, ?_, ?_, hlk, ⟨?_, ?_, ?_, ?_, ?_, mc, ?_⟩, ?_⟩
    all_goals try simp only [Tactic.rf]
    · exact e120.symm
    · exact (e _ (by tn) (by tn)).trans h112
    · exact shl3 (by omega)
    · exact (e _ (by tn) (by tn)).trans m152
    · exact (e _ (by tn) (by tn)).trans m144
    · exact (e _ (by tn) (by tn)).trans m136
    · exact (e _ (by tn) (by tn)).trans m128
    · rw [e120]; exact mb.mono hret1_14.1
    · rw [e120]; exact mn
    · exact baseM_sample hBM (by tn) (by tn)
        (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]) hret1_14 hret1_20 hret1_15
        ⟨hret1_16, hret1_17, hret1_18, hret1_19⟩


/-- **One element pushed**: a word stored at the buffer's next slot, the length stored, keep `Mem`, `BaseM` and
    the buffer's address. -/
theorem pushed {env : Env} {ret top : Word} {regs R : Reg → Word} {m M : MachineState} {v : Word}
    (hlim : env.stackLimit.toNat + 160 ≤ top.toNat) (hO0 : OwnedT env m top (regs .x11))
    (hMem : Mem env top regs m M) (hBM : BaseM env ret top regs m M)
    (hlt : (R .x23).toNat < (regs .x13).toNat) (h27 : (R .x27).toNat = 8 * (R .x23).toNat) :
    Mem env top regs m ((M.setMem (M.getMem (top + 18446744073709551496#64) + R .x27) v).setMem
        (top + 18446744073709551504#64) (R .x23 + 1#64)) ∧
      BaseM env ret top regs m ((M.setMem (M.getMem (top + 18446744073709551496#64) + R .x27) v).setMem
        (top + 18446744073709551504#64) (R .x23 + 1#64)) ∧
      ((M.setMem (M.getMem (top + 18446744073709551496#64) + R .x27) v).setMem
        (top + 18446744073709551504#64) (R .x23 + 1#64)).getMem (top + 18446744073709551496#64) =
        M.getMem (top + 18446744073709551496#64) := by
  obtain ⟨m152, m144, m136, m128, mb, mc, mn⟩ := hMem
  have hlay := env.layout
  have hnM := hBM.1.2.1
  obtain ⟨hp0, hpl, hpa⟩ := mb.resolve_left (by omega)
  unfold Env.Live at hpl
  have hA : (M.getMem (top + 18446744073709551496#64) + R .x27).toNat =
      (M.getMem (top + 18446744073709551496#64)).toNat + 8 * (R .x23).toNat := by
    rw [BitVec.toNat_add, h27]; omega
  have hna : M.getMem (top + 18446744073709551496#64) + R .x27 ≠ env.nextAddr := Tactic.ne_of_toNat (by omega)
  have hns : top + 18446744073709551504#64 ≠ env.nextAddr := Tactic.ne_of_toNat (by tn)
  have rd : ∀ c : Word, c ≠ 18446744073709551504#64 → env.stackLimit.toNat ≤ (top + c).toNat →
      ((M.setMem (M.getMem (top + 18446744073709551496#64) + R .x27) v).setMem
        (top + 18446744073709551504#64) (R .x23 + 1#64)).getMem (top + c) = M.getMem (top + c) := fun c hc h1 => by
    rw [MachineState.getMem_setMem_ne (fun he => hc ((BitVec.add_right_inj top).1 he)),
      MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega))]
  have hn : env.next ((M.setMem (M.getMem (top + 18446744073709551496#64) + R .x27) v).setMem
      (top + 18446744073709551504#64) (R .x23 + 1#64)) = env.next M := by
    rw [Tactic.next_setMem hns, Tactic.next_setMem hna]
  have r120 := rd 18446744073709551496#64 (by decide) (by tn)
  refine ⟨⟨(rd _ (by decide) (by tn)).trans m152, (rd _ (by decide) (by tn)).trans m144,
    (rd _ (by decide) (by tn)).trans m136, (rd _ (by decide) (by tn)).trans m128,
    by rw [r120]; exact mb.mono (by rw [hn]), mc, by rw [r120]; exact mn⟩, ?_, r120⟩
  exact baseM_store (baseM_store hBM hO0 hlim (.inr ⟨by omega, by omega⟩)) hO0 hlim (.inl ⟨by tn, by tn⟩)

set_option hygiene false in
/-- After a push, on to the exit: the length reached the count. -/
local macro "push_fin" : tactic => `(tactic| (
  rw [m136] at hc
  have hle := BitVec.le_def.1 hc
  refine hfin _ _ ⟨by rv_closeT, (hP _).1.1, ?_, ?_, ?_, ?_, (hP _).2.1⟩
  all_goals try simp only [Tactic.rf, MachineState.getMem_setMem_eq]
  · rw [(hP _).1.2.2.2.1]; exact (hP _).1.2.2.2.2.1
  · rw [(hP _).1.2.2.2.1]; exact mc
  · exact BitVec.eq_of_toNat_eq (by omega)
  · rw [(hP _).1.2.2.2.1]))

set_option hygiene false in
/-- After a push, on to `Sponge::sample`'s call: elements are left. -/
local macro "push_call" : tactic => `(tactic| (
  rw [m136] at hc
  have hle := BitVec.lt_def.1 hc
  refine hcall k (fun R' M' => ih k R' M' (by omega)) _ _ ⟨by rv_closeT, ?_, ?_, ?_, ?_, ?_, ?_, (hP _).1, (hP _).2.1⟩
  all_goals try simp only [Tactic.rf, MachineState.getMem_setMem_eq]
  · exact m144
  · exact m136
  · exact (hP _).2.2.symm
  · omega
  · omega))

set_option hygiene false in
/-- After a push, back to the head. -/
local macro "push_head" : tactic => `(tactic| (
  refine ih k _ _ (by omega) ⟨by rv_closeT, ?_, by rv_closeT, ?_, ?_, ?_, (hP _).1, (hP _).2.1⟩
  all_goals try simp only [Tactic.rf, MachineState.getMem_setMem_eq]
  · exact (hP _).2.2.symm
  · rw [toNat_add_ofNat (by omega), h27]; omega
  · omega))

set_option hygiene false in
/-- `grow_one`, never reached: the length is below the count, the capacity. -/
local macro "push_grow" : tactic => `(tactic| (
  exfalso; rw [m128] at hc; have := congrArg BitVec.toNat hc; omega))


set_option rv_sym.heap true in
/-- **The inner loop**, from its head: the exit when the vector is full, else one element pushed (its buffer has
    room: the capacity is the count), then back to the head, on to `Sponge::sample` when the word's bits are used
    up, or to the exit; one element fewer left. -/
theorem loop (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 160 ≤ need)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hC : Ctx env top regs m)
    (hcall : ∀ k, (∀ R M, LInv env ret top regs m k R M →
        rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 194, ret, top⟩ :: rest, R, M⟩) →
      ∀ R M, CInv env ret top regs m k R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 152, ret, top⟩ :: rest, R, M⟩)
    (hfin : ∀ R M, FinInv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 234, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, LInv env ret top regs m k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 194, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv env ret top regs m) fun k R M hI ih => ?_
  obtain ⟨-, -, -, h112, h27, hlk, ⟨m152, m144, m136, m128, mb, mc, mn⟩, hBM⟩ := id hI
  rv_introT hI
  rv_symT hp stop [146, 196] with [(by omega : env.stackLimit.toNat + 160 ≤ top.toNat)]
  -- the vector full: the exit
  · have hlen : R .x23 = regs .x13 := hc.symm
    have hk0 : k = 0 := by have := congrArg BitVec.toNat hc; omega
    clear hc
    rv_symT hp stop [152, 234] with [(by omega : env.stackLimit.toNat + 160 ≤ top.toNat)]
    · refine hfin _ _ ⟨by rv_closeT, m152, ?_, ?_, h112.trans hlen, ?_, hBM⟩
      · rw [m128]; exact mb
      · rw [m128]; exact mc
      · rw [m128]
    · exfalso; rw [m136, hlen] at hc; exact absurd hc (BitVec.lt_irrefl _)
  -- an element pushed
  · rcases k with _ | k
    · exact absurd (BitVec.eq_of_toNat_eq (by omega)) hc
    have hlt : (R .x23).toNat < (regs .x13).toNat := by omega
    clear hc
    obtain ⟨hp0, hpl, hpa⟩ := mb.resolve_left (by omega)
    unfold Env.Live at hpl
    have hA : (M.getMem (top + 18446744073709551496#64) + R .x27).toNat =
        (M.getMem (top + 18446744073709551496#64)).toNat + 8 * (R .x23).toNat := by
      rw [BitVec.toNat_add, h27]; omega
    have hP := fun v => pushed (v := v) (by omega) hC.tO ⟨m152, m144, m136, m128, mb, mc, mn⟩ hBM hlt h27
    have h1 : (R .x23 + 1#64).toNat = (R .x23).toNat + 1 := toNat_add_ofNat (by omega)
    rv_symT hp stop [152, 194, 224, 234] through [146, 176] with [(by omega : env.stackLimit.toNat + 160 ≤ top.toNat)]
    · push_fin
    · push_call
    · push_head
    · push_grow
    · push_fin
    · push_call
    · push_head
    · push_grow

/-- At the epilogue (instruction 248): the stack pointer, the frame, the code, the static data, the saved registers'
    slots, `PostK`. -/
def RetInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551456#64 ∧ env.Frame top (NextScalar.Out 24 regs m) m M ∧ M.code = m.code ∧
    env.Static M ∧ Saved ret top regs M ∧ PostK env regs m R M

set_option rv_sym.heap true in
/-- **The epilogue**: the saved registers restored, the return. -/
theorem ret_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostK env) (NextScalar.Out 24) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 160 ≤ need) (hal : top.toNat % 16 = 0)
    (hW : Windows env top m) :
    ∀ R M, RetInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 248, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  obtain ⟨-, hF, -, hS, ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13⟩, hK⟩ := id hinv
  rv_introT hinv
  rv_symT hp with [(by omega : env.stackLimit.toNat + 160 ≤ top.toNat)]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hF, hS, hK⟩ <;> simp only [Tactic.rf]
  exacts [s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13]

set_option hygiene false in
/-- `BaseM` at the prologue's memory: the frame, the saved registers' slots, the transcript kept. -/
local macro "pro_base" : tactic => `(tactic| (
  refine ⟨by rv_closeT, by rv_closeT, by rv_closeT, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  iterate 13 simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq]
  · exact (hC.tT.frameF hC.tO (by rv_closeT) hpre_5 (by omega)).1
  · exact (hC.tT.frameF hC.tO (by rv_closeT) hpre_5 (by omega)).2.1
  · exact (hC.tT.frameF hC.tO (by rv_closeT) hpre_5 (by omega)).2.2))

set_option rv_sym.heap true in
/-- **`sample_queries` returns `PostK`**: the power-of-two check (`Err` otherwise), the capacity's overflow check,
    the allocation, the de Bruijn lookup of the depth, then `Sponge::sample`'s first call and the loops, or the exit
    when the count is `0`. -/
theorem kept (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hdata : DataRef.InData env (tables L)) {need needS needA needH : Nat} (hnS : 160 + needS ≤ need)
    (hnA : 160 + needA ≤ need) (hnH : 160 + needH ≤ need)
    (hsa : SampleT.specT env p L.sample.idx needS) (hal : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA)
    (hhe : Aborts env p L.handleError.idx needH) :
    HoldsT env p i need (PreT env) (PostK env) (NextScalar.Out 24) (Stop := AbortStop) := by
  rv_autoT hp stop [2] with [hL, (by omega : env.stackLimit.toNat + 160 ≤ top.toNat)]
  have hC : Ctx env top regs m := hpre_2 ▸
    ⟨⟨⟨hpre_6, hpre_7, hpre_8, hpre_9⟩, hpre_10, hpre_11, hpre_12, hpre_13, hpre_14⟩,
      ⟨⟨hpre_15, hpre_16⟩, ⟨hpre_17, hpre_18⟩⟩, hpre_19, hpre_20, ⟨hpre_23, hpre_24⟩, hpre_21, hpre_22⟩
  clear hpre_6 hpre_7 hpre_8 hpre_9 hpre_10 hpre_11 hpre_12 hpre_13 hpre_14 hpre_15 hpre_16 hpre_17 hpre_18 hpre_19
    hpre_20 hpre_21 hpre_22 hpre_23 hpre_24
  rv_symT hp stop [48, 248] with [hL, (by omega : env.stackLimit.toNat + 160 ≤ top.toNat)]
  · rv_symT hp stop [72] with [hL, (by omega : env.stackLimit.toNat + 160 ≤ top.toNat)] using [hhe]
    have hov := ovf hc
    clear hc hc_1
    obtain ⟨hca, hcw, -⟩ : _ ∧ inWindow (L.d_c8_14ca7de5.hi + L.d_c8_14ca7de5.lo) 8 = true ∧ _ :=
      Hash.KeccakFT.table_range (ws := Gen.Verifier.Whir.SampleQueries.d_c8_14ca7de5_words)
      hpre_26 hpre_4 (hdata _ (List.mem_cons_self ..)) (by decide) (by decide)
    obtain ⟨-, hbw, -⟩ : _ ∧ inWindow (L.d_c64_b1d69b10.hi + L.d_c64_b1d69b10.lo) 64 = true ∧ _ :=
      Hash.KeccakFT.table_range (ws := Gen.Verifier.Whir.SampleQueries.d_c64_b1d69b10_words) hpre_26 hpre_4
      (hdata _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (by decide) (by decide)
    have hac : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
      hal.mono_stop fun _ _ _ _ _ h => h.1
    have e8 := shl3 (x := regs .x13) (by omega)
    rv_symT hp stop [152, 234] with [hL, (by omega : env.stackLimit.toNat + 160 ≤ top.toNat)] using [hac, hhe]
    -- `count = 0`: the empty vector, to the exit
    · refine fin_ok env p i L hp hk hpre_3 (by omega) hpre_25 hpre_26 hC _ _ ⟨by rv_closeT, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals try simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq]
      · exact .inl rfl
      · decide
      · exact hc.symm
      · rw [hc]
      · iterate 3 (refine baseM_store ?_ hC.tO (by omega) (.inl ⟨by tn, by tn⟩))
        pro_base
    -- `count << 3 = 0` with `count ≠ 0`: refuted by the overflow check
    · exact hcw
    · exact MerkleT.byte_in hbw _
    · exfalso; exact hc (BitVec.eq_of_toNat_eq (by
        have := congrArg BitVec.toNat hc_1; rw [e8] at this; simp only [BitVec.toNat_ofNat] at this ⊢; omega))
    -- allocated with `count = 0`: refuted
    · exfalso; exact hc_1 (by rw [hc]; decide)
    · exact hcw
    · exact MerkleT.byte_in hbw _
    -- the vector allocated, `Sponge::sample`'s first call
    · have hge := hpre_26.next_ge
      have hlay := env.layout
      have hn1 : (r1 .x10).toNat + (regs .x13).toNat * 8 = (env.next m1).toNat := by rw [← hret1_18, e8]; omega
      have hnm1 := hret1_14.2.1
      have hnm0 := hret1_14.1
      refine call_ok env p i L hp hL hnS hsa hstop hpre_3 hpre_25 hpre_26 (k := (regs .x13).toNat)
        (loop env p i L hp hpre_3 (by omega) hpre_25 hpre_26 hC
          (fun k h => call_ok env p i L hp hL hnS hsa hstop hpre_3 hpre_25 hpre_26 h)
          (fin_ok env p i L hp hk hpre_3 (by omega) hpre_25 hpre_26 hC) _) _ _
        ⟨by rv_closeT, by rv_closeT, by rv_closeT, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, hov, ?_⟩, ?_⟩
      all_goals try simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq, Tactic.rf]
      · simp
      · exact Nat.pos_of_ne_zero fun h => hc (BitVec.eq_of_toNat_eq h)
      · exact (hret1_14.getMem_above (a := top + 18446744073709551464#64) (by tn)
          (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat]; omega) id).trans
          (by simp only [MachineState.getMem_setMem_eq])
      · refine .inr ⟨by omega, ?_, hret1_17⟩
        unfold Env.Live
        repeat (rw [Env.next_setMem_stack]; rotate_left; tn)
        omega
      · exact hret1_16
      · iterate 5 (refine baseM_store ?_ hC.tO (by omega) (.inl ⟨by tn, by tn⟩))
        refine baseM_callF ?_ (by tn) (by tn) hret1_14 hret1_19 hret1_15
        pro_base
  · -- `Err(NotPowerOfTwo)`
    have hlS := hC.wS.lt
    have hlT := hC.tT.2.1.lt
    have hwS := hC.wS
    have o0 : NextScalar.Out 24 regs m (regs .x10) := Or.inl ⟨Nat.le_refl _, by omega⟩
    have o8 : NextScalar.Out 24 regs m (regs .x10 + 8#64) :=
      Or.inl ⟨by rw [toNat_add_ofNat (by omega)]; omega, by rw [toNat_add_ofNat (by omega)]; omega⟩
    refine ret_ok env p i L hp hk hpre_3 (by omega) hpre_25 hpre_26 _ _
      ⟨by rv_closeT, Tactic.frame_out (Tactic.frame_out (by rv_closeT) o0 (hwS.ne_next (Nat.le_refl _) (by omega))) o8
        (hwS.ne_next_add (o := 8) (by omega)), by rv_closeT, by rv_closeT, ⟨
        (rd_slot2 (x := top + 18446744073709551608#64) hC.oS hpre_5 (by tn) (by tn)).trans ?_,
        (rd_slot2 (x := top + 18446744073709551600#64) hC.oS hpre_5 (by tn) (by tn)).trans ?_,
        (rd_slot2 (x := top + 18446744073709551592#64) hC.oS hpre_5 (by tn) (by tn)).trans ?_,
        (rd_slot2 (x := top + 18446744073709551584#64) hC.oS hpre_5 (by tn) (by tn)).trans ?_,
        (rd_slot2 (x := top + 18446744073709551576#64) hC.oS hpre_5 (by tn) (by tn)).trans ?_,
        (rd_slot2 (x := top + 18446744073709551568#64) hC.oS hpre_5 (by tn) (by tn)).trans ?_,
        (rd_slot2 (x := top + 18446744073709551560#64) hC.oS hpre_5 (by tn) (by tn)).trans ?_,
        (rd_slot2 (x := top + 18446744073709551552#64) hC.oS hpre_5 (by tn) (by tn)).trans ?_,
        (rd_slot2 (x := top + 18446744073709551544#64) hC.oS hpre_5 (by tn) (by tn)).trans ?_,
        (rd_slot2 (x := top + 18446744073709551536#64) hC.oS hpre_5 (by tn) (by tn)).trans ?_,
        (rd_slot2 (x := top + 18446744073709551528#64) hC.oS hpre_5 (by tn) (by tn)).trans ?_,
        (rd_slot2 (x := top + 18446744073709551520#64) hC.oS hpre_5 (by tn) (by tn)).trans ?_,
        (rd_slot2 (x := top + 18446744073709551512#64) hC.oS hpre_5 (by tn) (by tn)).trans ?_⟩, ?_, ?_⟩
    iterate 13 simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq]
    · refine spongeT_err hC.wS ?_ hC.apST hlT
      exact (hC.tT.frameF hC.tO (by rv_closeT) hpre_5 (by omega)).1.1
    · intro h
      exact absurd (by
        rw [MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by rw [toNat_add_ofNat (by omega)]; omega)),
          MachineState.getMem_setMem_eq]) h

/-- **`sample_queries` is total**, from `kept` and `TOut`'s frame (`TranscriptAtT.frameS`). -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hdata : DataRef.InData env (tables L)) {need needS needA needH : Nat} (hnS : 160 + needS ≤ need)
    (hnA : 160 + needA ≤ need) (hnH : 160 + needH ≤ need)
    (hsa : SampleT.specT env p L.sample.idx needS) (hal : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA)
    (hhe : Aborts env p L.handleError.idx needH) : specT env p i need :=
  Isa.TContract.mono (kept env p i L hp hL hdata hnS hnA hnH hsa hal hhe) (fun _ _ _ _ h => h)
    (fun _ top regs m _ _ ⟨⟨he, hs, _, hn, hP, _⟩, _⟩ ⟨⟨ha, hf, hst', hK, hV⟩, hc⟩ => by
      have hT := hP.1.1.frameS hK (he.2 ▸ hP.1.2.1) hf hn (by omega) (NextScalarT.out_miss hP.1).1
        (NextScalarT.out_miss hP.1).2
      exact ⟨⟨ha, hf, hst', hT.1, he.2 ▸ hT.2.1, hT.2.2, hV⟩, hc⟩)
    fun _ _ _ _ _ _ _ h => h

end Rv64mc.Proof.Whir.SampleQueriesT

/-- info: 'Rv64mc.Proof.Whir.SampleQueriesT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Whir.SampleQueriesT.total
