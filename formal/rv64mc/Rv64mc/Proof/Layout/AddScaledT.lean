/-
  Rv64mc.Proof.Layout.AddScaledT

  `Form::add_scaled(&mut self, other, weight)` is total: called with `self` (`a0`), `other`'s terms (`a1`, `a2`, the
  slice of 40-byte terms LLVM passes for `&Form`) and the weight (`a3`, `a4`), it takes each of `other`'s terms in
  turn, finds where its monomial goes in `self`'s sorted terms (`AddScaledSearchT.search`), and either adds the
  weighted coefficient to the term there (after `memcmp` finds the monomials equal and `E::mul`) or inserts a new
  term: the monomial cloned (`Vec<usize>::clone`), the coefficient weighted, the buffer grown when full
  (`RawVec::grow_one`) and the later terms moved one place up (`memmove`). `self` stays a `Form` (`FormT`) and its
  buffer the entry's or one allocated since (`PairT.KeptOrFresh`); the run ends with the guest's abort (`AbortStop`)
  where `clone` or `grow_one` does. A safety-only contract (the function is class D: no spec); it does not state
  the terms' values.

  The precondition: `self` a `Form` its caller owns; `other`'s terms a buffer's (`BufT`, the length for the
  capacity), each monomial a vector (`TermsT`); `self`'s header apart from its buffer, and `other`'s terms apart
  from both (`PairT.Apart`), which Rust's `&mut self` against `&Form` gives. What it writes besides its stack and
  fresh blocks is `self`'s header and its buffer at the entry (`OutT`).

  The body is cut at the outer loop's head (instruction 25, measure `other`'s terms left), instruction 54 (the
  search's index), the insertion (86 and 87), the buffer's reload (104), the new term's stores (116) and the
  return (162). Every part keeps `MemOk` (the thirteen slots, the frame, the static data, the code).

  ## Main definitions

  * `PreT`, `PostT`, `OutT`, `SpecT`, `Slots`, `MemOk`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Layout.AddScaledSearchT
import Rv64mc.Proof.Layout.PairT
import Rv64mc.Proof.Layout.CloneFormsT
import Rv64mc.Proof.Runtime.MemcmpT
import Rv64mc.Proof.Runtime.MemmoveT
import Rv64mc.Proof.Field.EMulT

namespace Rv64mc.Proof.Layout.AddScaledT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT RawVecT VecT)
open Rv64mc.Proof.Runtime.CloneT (ClonePostT CloneSpecT)
open Rv64mc.Proof.Runtime.GrowOneT (GrowOneSpecT)
open Rv64mc.Proof.Runtime.MemcmpT (MemcmpSpecT)
open Rv64mc.Proof.Runtime.MemmoveT (MemmoveSpecT)
open Rv64mc.Proof.Layout.FormReprT
open Rv64mc.Proof.Layout.PairT (Apart KeptOrFresh)
open Rv64mc.Proof.Layout.AddScaledSearchT (SKeep search inWin_word sh40 sh40' termT)
open Rv64mc.Proof.Runtime.GrowOne (rvCapAt_eq rvPtrAt_eq)
open Rv64mc.Proof.Runtime.VecHdrT (vecCap_eq vecPtr_eq vecLen_eq)
open Rv64mc.Gen.Verifier.Layout.Form.AddScaled (Link tmpl)

/-- The total precondition: `self` (`a0`) a `Form` its caller owns, its header apart from its buffer; `other`'s
    terms (`a1`, `a2`) a buffer's, each monomial a vector, apart from `self`'s header and buffer. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  FormT env m (regs .x10) ∧ env.Owned m (regs .x2) (regs .x10) 24 ∧
    BufT env m (regs .x12) (regs .x11) 40 ∧ TermsT env m (regs .x11) (regs .x12).toNat ∧
    ((vecCap m (regs .x10)).toNat = 0 ∨
      Apart (regs .x10) 24 (vecPtr m (regs .x10)) (40 * (vecCap m (regs .x10)).toNat)) ∧
    ((regs .x12).toNat = 0 ∨ (Apart (regs .x11) (40 * (regs .x12).toNat) (regs .x10) 24 ∧
      ((vecCap m (regs .x10)).toNat = 0 ∨
        Apart (regs .x11) (40 * (regs .x12).toNat) (vecPtr m (regs .x10)) (40 * (vecCap m (regs .x10)).toNat))))

/-- The total postcondition: `self` a `Form` again, its buffer the entry's or allocated since. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  FormT env m' (regs .x10) ∧ KeptOrFresh env m m' (regs .x10)

/-- What `add_scaled` writes besides its stack and what it allocates: `self`'s header and its buffer at the
    entry. -/
def OutT (regs : Reg → Word) (m : MachineState) (b : Word) : Prop :=
  InRange (regs .x10) 24 b ∨ InRange (vecPtr m (regs .x10)) (40 * (vecCap m (regs .x10)).toNat) b

/-- **The total contract of `Form::add_scaled`**, or the guest's abort. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) OutT AbortStop

/-! ## The frame -/

/-- The prologue's thirteen saved words in `M`, at `top - 8` down to `top - 104`. -/
def Slots (M : MachineState) (top ret : Word) (regs : Reg → Word) : Prop :=
  M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551560#64) = regs .x21 ∧ M.getMem (top + 18446744073709551552#64) = regs .x22 ∧
    M.getMem (top + 18446744073709551544#64) = regs .x23 ∧ M.getMem (top + 18446744073709551536#64) = regs .x24 ∧
    M.getMem (top + 18446744073709551528#64) = regs .x25 ∧ M.getMem (top + 18446744073709551520#64) = regs .x26 ∧
    M.getMem (top + 18446744073709551512#64) = regs .x27

/-- What every part keeps of memory: the slots, the frame, the static data, the code. -/
def MemOk (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (M : MachineState) : Prop :=
  Slots M top ret regs ∧ env.Frame top (OutT regs m) m M ∧ env.Static M ∧ M.code = m.code

/-- The facts of the entry every part reads. -/
def Args (env : Env) (m : MachineState) (top : Word) (regs : Reg → Word) : Prop :=
  env.stackLimit.toNat + 144 ≤ top.toNat ∧ Windows env top m ∧ top.toNat % 16 = 0 ∧ regs .x2 = top ∧
    PreT env regs m

theorem slots_keep {M X : MachineState} {top ret : Word} {regs : Reg → Word} (hlim : 144 ≤ top.toNat)
    (hk : ∀ a : Word, top.toNat - 104 ≤ a.toNat → a.toNat < top.toNat → X.getMem a = M.getMem a)
    (hsl : Slots M top ret regs) : Slots X top ret regs := by
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 104 → X.getMem (top + c) = M.getMem (top + c) :=
    fun c k hc h0 hk' => by
      have e := CloneFormsT.es (top := top) hc (by omega)
      exact hk _ (by rw [e]; omega) (by rw [e]; omega)
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13⟩ := hsl
  exact ⟨(g _ 8 rfl (by omega) (by omega)).trans s1, (g _ 16 rfl (by omega) (by omega)).trans s2,
    (g _ 24 rfl (by omega) (by omega)).trans s3, (g _ 32 rfl (by omega) (by omega)).trans s4,
    (g _ 40 rfl (by omega) (by omega)).trans s5, (g _ 48 rfl (by omega) (by omega)).trans s6,
    (g _ 56 rfl (by omega) (by omega)).trans s7, (g _ 64 rfl (by omega) (by omega)).trans s8,
    (g _ 72 rfl (by omega) (by omega)).trans s9, (g _ 80 rfl (by omega) (by omega)).trans s10,
    (g _ 88 rfl (by omega) (by omega)).trans s11, (g _ 96 rfl (by omega) (by omega)).trans s12,
    (g _ 104 rfl (by omega) (by omega)).trans s13⟩

variable {env : Env}

/-- **A store into `self`'s current buffer** `[P, P + 40 C)`, the entry's or fresh: `MemOk`, `NEXT` and every other
    word kept. -/
theorem buf_store {m M : MachineState} {top ret b v P C : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 144 ≤ top.toNat) (hM : MemOk env m top ret regs M)
    (hkf : (P = vecPtr m (regs .x10) ∧ C = vecCap m (regs .x10)) ∨ (env.next m).toNat ≤ P.toNat)
    (hb1 : P.toNat ≤ b.toNat) (hb2 : b.toNat < P.toNat + 40 * C.toNat)
    (hlive : P.toNat + 40 * C.toNat ≤ (env.next M).toNat) :
    MemOk env m top ret regs (M.setMem b v) ∧ env.next (M.setMem b v) = env.next M ∧
      ∀ c : Word, c ≠ b → (M.setMem b v).getMem c = M.getMem c := by
  have hlay := env.layout
  obtain ⟨hsl, hF, hS, hc⟩ := hM
  have hnM := hF.2.1
  have hne : b ≠ env.nextAddr := fun e => by rw [e] at hb2; omega
  refine ⟨⟨slots_keep (by omega) (fun c h1 _ => MachineState.getMem_setMem_ne fun e => by rw [e] at h1; omega) hsl,
    ?_, Tactic.static_store hS (.inl (by omega)), by rw [MachineState.code_setMem, hc]⟩, Tactic.next_setMem hne,
    fun c hc => MachineState.getMem_setMem_ne hc⟩
  rcases hkf with ⟨hp, hcap⟩ | hfr
  · exact Tactic.frame_out hF (.inr ⟨by rw [← hp]; exact hb1, by rw [← hp, ← hcap]; exact hb2⟩) hne
  · exact Tactic.frame_fresh hF rfl (by omega) (by omega)

/-- **A store into `self`'s header**: `MemOk`, `NEXT` and every other word kept. -/
theorem hdr_store {m M : MachineState} {top ret b v : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 144 ≤ top.toNat) (hM : MemOk env m top ret regs M)
    (hown : env.Owned m top (regs .x10) 24) (hwin : InWin env (regs .x10) 24)
    (hb : InRange (regs .x10) 24 b) :
    MemOk env m top ret regs (M.setMem b v) ∧ env.next (M.setMem b v) = env.next M ∧
      ∀ c : Word, c ≠ b → (M.setMem b v).getMem c = M.getMem c := by
  have hlay := env.layout
  obtain ⟨hsl, hF, hS, hc⟩ := hM
  have hnm := hF.1
  have hnM := hF.2.1
  have hne : b ≠ env.nextAddr := hown.not_next (by omega) (by omega) hb
  obtain ⟨h1, h2⟩ := hb
  unfold InWin at hwin
  refine ⟨⟨slots_keep (by omega) (fun c h3 h4 => MachineState.getMem_setMem_ne fun e => by
      rw [e] at h3 h4; rcases hown.1 with h | h <;> omega) hsl,
    Tactic.frame_out hF (.inl ⟨h1, h2⟩) hne, Tactic.static_store hS (by omega),
    by rw [MachineState.code_setMem, hc]⟩, Tactic.next_setMem hne, fun c hc => MachineState.getMem_setMem_ne hc⟩

/-- **A call from the frame's bottom** (`top - 144`) writing at most `out'`, each a word `MemOk`'s frame allows and
    apart from the slots: `MemOk` kept, every word below `NEXT` or at or above `top - 144` and outside `out'` kept. -/
theorem call_keep {m M M' : MachineState} {top ret : Word} {regs : Reg → Word} {out' : Word → Prop}
    (hlim : env.stackLimit.toNat + 144 ≤ top.toNat) (hM : MemOk env m top ret regs M)
    (hF : env.Frame (top + 18446744073709551472#64) out' M M') (hSt : env.Static M') (hc : M'.code = M.code)
    (hout : ∀ b, out' b → env.MayWrite top (OutT regs m) m M' b ∧ (b.toNat < top.toNat - 104 ∨ top.toNat ≤ b.toNat))
    (hkeep : ∀ a : Word, a.toNat < (env.next M).toNat ∨ (top + 18446744073709551472#64).toNat ≤ a.toNat → ¬ out' a →
      M'.getMem a = M.getMem a) :
    MemOk env m top ret regs M' ∧ (env.next M).toNat ≤ (env.next M').toNat ∧
      ∀ a : Word, (a.toNat < (env.next M).toNat ∨ top.toNat - 144 ≤ a.toNat) → ¬ out' a →
        M'.getMem a = M.getMem a := by
  have hlay := env.layout
  obtain ⟨hsl, hF0, -, hc0⟩ := hM
  have e144 := CloneFormsT.es (top := top) (c := 18446744073709551472#64) (k := 144) rfl (by omega)
  have hk : ∀ a : Word, (a.toNat < (env.next M).toNat ∨ top.toNat - 144 ≤ a.toNat) → ¬ out' a →
      M'.getMem a = M.getMem a := fun a h1 h2 => hkeep a (by rw [e144]; exact h1) h2
  refine ⟨⟨slots_keep (by omega) (fun a h1 _ => hk a (.inr (by omega)) fun ho => by
      have := (hout a ho).2; omega) hsl,
    hF0.trans hF (by rw [e144]; omega) fun b hb => (hout b hb).1, hSt, hc.trans hc0⟩, hF.1, hk⟩

/-! ## `self`'s and `other`'s blocks -/

/-- `n` terms from `P` with a gap at `j`: the `j` before and the `n - j` after (from `j + 1`), each monomial a
    vector. -/
def GapT (env : Env) (M : MachineState) (P : Word) (n j : Nat) : Prop :=
  ∀ t, t ≤ n → t ≠ j → VecT env M (P + BitVec.ofNat 64 (40 * t)) 8

/-- `self`'s current buffer, from its header: none, or from `0x10000000`, below `NEXT`, 8-byte aligned. -/
theorem buf_foot {M : MachineState} {a : Word} (hV : VecT env M a 40) :
    (M.getMem a).toNat = 0 ∨ (0x10000000 ≤ (M.getMem (a + 8#64)).toNat ∧
      (M.getMem (a + 8#64)).toNat + 40 * (M.getMem a).toNat ≤ (env.next M).toNat ∧
      (M.getMem (a + 8#64)).toNat % 8 = 0) := by
  have h := hV.2.1.2.2.1
  rw [rvCapAt_eq, rvPtrAt_eq] at h
  rcases h with h | ⟨h1, h2, h3⟩
  · exact .inl h
  · unfold Env.Live at h2; exact .inr ⟨h1, by omega, h3⟩

/-- **`self`'s header apart from its current buffer**, the entry's (`PreT`) or fresh (the header is the caller's:
    below `NEXT` at the entry, or on the stack). -/
theorem hdr_apart {m M : MachineState} {top ret : Word} {regs : Reg → Word} (hA : Args env m top regs)
    (hM : MemOk env m top ret regs M) (hkf : KeptOrFresh env m M (regs .x10)) (hV : VecT env M (regs .x10) 40) :
    (M.getMem (regs .x10)).toNat = 0 ∨
      Apart (regs .x10) 24 (M.getMem (regs .x10 + 8#64)) (40 * (M.getMem (regs .x10)).toNat) := by
  have hlay := env.layout
  obtain ⟨hstk, -, -, hx2, -, hown, -, -, hha, -⟩ := hA
  rw [hx2] at hown
  have hnM := hM.2.1.2.1
  rcases hkf with ⟨hp, hc⟩ | hfr
  · rw [vecPtr_eq] at hp; rw [vecCap_eq, vecCap_eq] at hc
    rw [hp, hc]; rw [vecPtr_eq, vecCap_eq] at hha; exact hha
  · rw [vecPtr_eq] at hfr
    rcases buf_foot hV with h | ⟨-, h2, -⟩
    · exact .inl h
    · right; unfold Apart; rcases hown.1 with h | h <;> omega

/-- **`other`'s terms are kept**: below `NEXT` at the entry and apart from `self`'s header and buffer there. -/
theorem oth_kept {m M : MachineState} {top ret : Word} {regs : Reg → Word} (hA : Args env m top regs)
    (hM : MemOk env m top ret regs M) :
    ∀ b : Word, (regs .x11).toNat ≤ b.toNat → b.toNat < (regs .x11).toNat + 40 * (regs .x12).toNat →
      M.getMem b = m.getMem b := by
  intro b h1 h2
  have hlay := env.layout
  obtain ⟨hstk, hW, -, -, -, -, hsrc, -, -, hap⟩ := hA
  have hnx : (env.next m).toNat ≤ env.heapEnd.toNat := hM.2.1.1.trans hM.2.1.2.1
  have hlive : (regs .x11).toNat + 40 * (regs .x12).toNat ≤ (env.next m).toNat := by
    rcases hsrc with h | ⟨-, h, -⟩
    · omega
    · unfold Env.Live at h; omega
  refine hM.2.1.getMem_below_next hnx (by omega) fun ho => ?_
  rcases hap with h | ⟨ha1, ha2⟩
  · omega
  · rcases ho with ⟨o1, o2⟩ | ⟨o1, o2⟩
    · unfold Apart at ha1; omega
    · rcases ha2 with h | h
      · omega
      · unfold Apart at h; omega

/-- **`other`'s terms' monomials are vectors**, in any memory `MemOk` reaches. -/
theorem oth_terms {m M : MachineState} {top ret : Word} {regs : Reg → Word} (hA : Args env m top regs)
    (hM : MemOk env m top ret regs M) : TermsT env M (regs .x11) (regs .x12).toNat := by
  have hlay := env.layout
  obtain ⟨-, hW, -, -, -, -, hsrc, hterms, -, -⟩ := id hA
  have hlive : (regs .x12).toNat = 0 ∨ (regs .x11).toNat + 40 * (regs .x12).toNat ≤ (env.next m).toNat := by
    rcases hsrc with h | ⟨-, h, -⟩
    · exact .inl h
    · unfold Env.Live at h; exact .inr (by omega)
  rcases hlive with h0 | hl
  · intro t ht; omega
  · exact CloneFormsT.TermsT.keep hterms (by have := hW.heapEnd_le; omega) hM.2.1.1 (oth_kept hA hM)

/-- **The new term's six stores**: the coefficient's two words and the clone `S`'s header at `T = P + 40 j` in
    `self`'s current buffer with room, then the length `n + 1`: `MemOk`, `NEXT`, the buffer kept, `self` a `Form`
    of `n + 1` terms. -/
theorem term_mem {m M : MachineState} {top ret P n T S v3 v4 : Word} {regs : Reg → Word} {j : Nat}
    (hlim : env.stackLimit.toNat + 144 ≤ top.toNat) (hA : Args env m top regs) (hM : MemOk env m top ret regs M)
    (hkf : KeptOrFresh env m M (regs .x10)) (hV : VecT env M (regs .x10) 40)
    (hP : M.getMem (regs .x10 + 8#64) = P) (hcap : n.toNat < (M.getMem (regs .x10)).toNat)
    (hT : T.toNat = P.toNat + 40 * j) (hj : j ≤ n.toNat) (hgap : GapT env M P n.toNat j) (hC : VecT env M S 8) :
    let M6 := (((((M.setMem (T + 32#64) v4).setMem T (M.getMem S)).setMem (T + 8#64) (M.getMem (S + 8#64))).setMem
      (T + 16#64) (M.getMem (S + 16#64))).setMem (T + 24#64) v3).setMem (regs .x10 + 16#64) (n + 1#64)
    MemOk env m top ret regs M6 ∧ env.next M6 = env.next M ∧ M6.getMem (regs .x10 + 8#64) = P ∧
      FormT env M6 (regs .x10) ∧ KeptOrFresh env m M6 (regs .x10) := by
  intro M6
  have hlay := env.layout
  obtain ⟨-, hW, -, hx2, -, hown, -, -, -, -⟩ := id hA
  rw [hx2] at hown
  have hha := hdr_apart hA hM hkf hV
  have hnM := hM.2.1.2.1
  have hlt := vecT_lt hV
  obtain ⟨hP1, hP2, hP8⟩ := (buf_foot hV).resolve_left (by omega)
  rw [hP] at hP1 hP2 hP8
  replace hha : Apart (regs .x10) 24 P (40 * (M.getMem (regs .x10)).toNat) := by
    rcases hha with h | h
    · omega
    · rw [← hP]; exact h
  unfold Apart at hha
  have hkf' : (P = vecPtr m (regs .x10) ∧ M.getMem (regs .x10) = vecCap m (regs .x10)) ∨
      (env.next m).toNat ≤ P.toNat := by
    rw [← hP, ← vecPtr_eq, ← vecCap_eq]; exact hkf
  have e8 : (T + 8#64).toNat = T.toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (T + 16#64).toNat = T.toNat + 16 := toNat_add_ofNat (by omega)
  have e24 : (T + 24#64).toNat = T.toNat + 24 := toNat_add_ofNat (by omega)
  have e32 : (T + 32#64).toNat = T.toNat + 32 := toNat_add_ofNat (by omega)
  have a8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
  have a16 : (regs .x10 + 16#64).toNat = (regs .x10).toNat + 16 := toNat_add_ofNat (by omega)
  have hb : ∀ x : Word, T.toNat ≤ x.toNat → x.toNat < T.toNat + 40 → P.toNat ≤ x.toNat ∧
      x.toNat < P.toNat + 40 * (M.getMem (regs .x10)).toNat := fun x h1 h2 => ⟨by omega, by omega⟩
  obtain ⟨m1, n1, k1⟩ := buf_store (b := T + 32#64) (v := v4) hlim hM hkf' (hb _ (by omega) (by omega)).1
    (hb _ (by omega) (by omega)).2 hP2
  obtain ⟨m2, n2, k2⟩ := buf_store (b := T) (v := M.getMem S) hlim m1 hkf' (hb _ (by omega) (by omega)).1
    (hb _ (by omega) (by omega)).2 (by rw [n1]; exact hP2)
  obtain ⟨m3, n3, k3⟩ := buf_store (b := T + 8#64) (v := M.getMem (S + 8#64)) hlim m2 hkf' (hb _ (by omega) (by omega)).1
    (hb _ (by omega) (by omega)).2 (by rw [n2, n1]; exact hP2)
  obtain ⟨m4, n4, k4⟩ := buf_store (b := T + 16#64) (v := M.getMem (S + 16#64)) hlim m3 hkf' (hb _ (by omega) (by omega)).1
    (hb _ (by omega) (by omega)).2 (by rw [n3, n2, n1]; exact hP2)
  obtain ⟨m5, n5, k5⟩ := buf_store (b := T + 24#64) (v := v3) hlim m4 hkf' (hb _ (by omega) (by omega)).1
    (hb _ (by omega) (by omega)).2 (by rw [n4, n3, n2, n1]; exact hP2)
  obtain ⟨m6, n6, k6⟩ := hdr_store (b := regs .x10 + 16#64) (v := n + 1#64) hlim m5 hown hV.1 ⟨by omega, by omega⟩
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  have hN : env.next M6 = env.next M := by rw [n6, n5, n4, n3, n2, n1]
  have hk : ∀ x : Word, (x.toNat < T.toNat ∨ T.toNat + 40 ≤ x.toNat) →
      (x.toNat < (regs .x10).toNat + 16 ∨ (regs .x10).toNat + 24 ≤ x.toNat) → M6.getMem x = M.getMem x :=
    fun x h1 h2 => by
      rw [k6 x (ne _ _ (by omega)), k5 x (ne _ _ (by omega)), k4 x (ne _ _ (by omega)), k3 x (ne _ _ (by omega)),
        k2 x (ne _ _ (by omega)), k1 x (ne _ _ (by omega))]
  have g0 : M6.getMem (regs .x10) = M.getMem (regs .x10) := hk _ (by omega) (by omega)
  have g8 : M6.getMem (regs .x10 + 8#64) = P := (hk _ (by omega) (by omega)).trans hP
  have g16 : M6.getMem (regs .x10 + 16#64) = n + 1#64 := MachineState.getMem_setMem_eq
  have gT : M6.getMem T = M.getMem S := by
    rw [k6 _ (ne _ _ (by omega)), k5 _ (ne _ _ (by omega)), k4 _ (ne _ _ (by omega)), k3 _ (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  have gT8 : M6.getMem (T + 8#64) = M.getMem (S + 8#64) := by
    rw [k6 _ (ne _ _ (by omega)), k5 _ (ne _ _ (by omega)), k4 _ (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  have gT16 : M6.getMem (T + 16#64) = M.getMem (S + 16#64) := by
    rw [k6 _ (ne _ _ (by omega)), k5 _ (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  have en1 : (n + 1#64).toNat = n.toNat + 1 := toNat_add_ofNat (by omega)
  have hV6 : VecT env M6 (regs .x10) 40 := by
    obtain ⟨w1, w2, w3⟩ := hV
    refine ⟨w1, w2.keep (by rw [rvCapAt_eq]; exact g0) (by rw [rvPtrAt_eq]; exact g8.trans hP.symm)
      (by rw [hN]), ?_⟩
    rw [vecLen_eq, vecCap_eq, g16, g0, en1]; omega
  refine ⟨m6, hN, g8, ⟨hV6, ?_⟩, ?_⟩
  · rw [vecPtr_eq, vecLen_eq, g8, g16, en1]
    intro t ht
    have et : (P + BitVec.ofNat 64 (40 * t)).toNat = P.toNat + 40 * t := toNat_add_ofNat (by omega)
    rcases Nat.lt_or_ge t j with htj | htj
    · refine vecT_keep (hgap t (by omega) (by omega)) (by rw [hN]) fun x h1 h2 => hk x ?_ ?_
      · rw [et] at h1 h2; omega
      · rw [et] at h1 h2; omega
    rcases Nat.lt_or_ge j t with htj' | htj'
    · refine vecT_keep (hgap t (by omega) (by omega)) (by rw [hN]) fun x h1 h2 => hk x ?_ ?_
      · rw [et] at h1 h2; omega
      · rw [et] at h1 h2; omega
    · have hTt : P + BitVec.ofNat 64 (40 * t) = T := BitVec.eq_of_toNat_eq (by rw [et]; omega)
      rw [hTt]
      exact CloneFormsT.vecT_copy hC (Runtime.MemsetT.InWin.sub (Or.inl ⟨hP1, by have := hW.heapEnd_le; omega⟩)
        (x := T) (n := 40 * (M.getMem (regs .x10)).toNat) (by omega) (by omega)) (by omega) (by rw [hN]) gT gT8 gT16
  · have ep : vecPtr M6 (regs .x10) = vecPtr M (regs .x10) := g8.trans hP.symm
    have ec : vecCap M6 (regs .x10) = vecCap M (regs .x10) := by rw [vecCap_eq, vecCap_eq]; exact g0
    unfold KeptOrFresh
    rw [ep, ec]
    exact hkf

/-! ## The later terms moved -/

/-- **After the later terms moved**: `memmove` of the `n - j` terms from `Src = P + 40 j` one term up, writing at
    most the doublewords of its destination (`out'`): `MemOk`, `self`'s header and the clone's kept, the terms but
    `j` monomials' vectors (`GapT`). -/
theorem move_mem {m M m1 : MachineState} {top ret P Src S : Word} {regs : Reg → Word} {out' : Word → Prop}
    {n j : Nat} (hlim : env.stackLimit.toNat + 144 ≤ top.toNat) (hA : Args env m top regs)
    (hM : MemOk env m top ret regs M) (hkf : KeptOrFresh env m M (regs .x10)) (hF : FormT env M (regs .x10))
    (hP : M.getMem (regs .x10 + 8#64) = P) (hn : (M.getMem (regs .x10 + 16#64)).toNat = n)
    (hcap : n < (M.getMem (regs .x10)).toNat) (hj : j < n) (hSrc : Src.toNat = P.toNat + 40 * j)
    (hS : top.toNat - 144 ≤ S.toNat) (hC : VecT env M S 8)
    (hF1 : env.Frame (top + 18446744073709551472#64) out' M m1)
    (hout : ∀ b, out' b → DwordsOf (Src + 40#64) (40 * (n - j)) b) (hSt : env.Static m1) (hc : m1.code = M.code)
    (hcopy : ∀ k < 40 * (n - j), m1.getByte (Src + 40#64 + BitVec.ofNat 64 k) = M.getByte (Src + BitVec.ofNat 64 k)) :
    MemOk env m top ret regs m1 ∧ (env.next M).toNat ≤ (env.next m1).toNat ∧
      m1.getMem (regs .x10) = M.getMem (regs .x10) ∧ m1.getMem (regs .x10 + 8#64) = P ∧
      m1.getMem (regs .x10 + 16#64) = M.getMem (regs .x10 + 16#64) ∧ GapT env m1 P n j ∧ VecT env m1 S 8 := by
  have hlay := env.layout
  obtain ⟨-, hW, -, hx2, -, hown, -, -, -, -⟩ := id hA
  rw [hx2] at hown
  have hW1 := hW.heapEnd_le
  have hha := hdr_apart hA hM hkf hF.1
  have hnM := hM.2.1.2.1
  have hnm := hM.2.1.1
  have hlt := vecT_lt hF.1
  obtain ⟨hP1, hP2, hP8⟩ := (buf_foot hF.1).resolve_left (by omega)
  rw [hP] at hP1 hP2 hP8
  replace hha : Apart (regs .x10) 24 P (40 * (M.getMem (regs .x10)).toNat) := by
    rcases hha with h | h
    · omega
    · rw [← hP]; exact h
  unfold Apart at hha
  have e144 := CloneFormsT.es (top := top) (c := 18446744073709551472#64) (k := 144) rfl (by omega)
  have eD : (Src + 40#64).toNat = P.toNat + 40 * j + 40 := by rw [toNat_add_ofNat (by omega), hSrc]
  have hD8 : (Src + 40#64).toNat % 8 = 0 := by omega
  have hin : ∀ b, out' b → (Src + 40#64).toNat ≤ b.toNat ∧ b.toNat < (Src + 40#64).toNat + 40 * (n - j) :=
    fun b hb => by
      have h := hout b hb
      unfold DwordsOf InRange at h
      rw [toNat_alignToDword] at h
      omega
  have hkf' : (P = vecPtr m (regs .x10) ∧ M.getMem (regs .x10) = vecCap m (regs .x10)) ∨
      (env.next m).toNat ≤ P.toNat := by
    rw [← hP, ← vecPtr_eq, ← vecCap_eq]; exact hkf
  obtain ⟨m1', n1, k1⟩ := call_keep hlim hM hF1 hSt hc (fun b hb => by
    have h := hin b hb
    refine ⟨?_, .inl (by omega)⟩
    rcases hkf' with ⟨hp, hcp⟩ | hfr
    · exact Or.inr (Or.inr (Or.inr (.inr ⟨by rw [← hp]; omega, by rw [← hp, ← hcp]; omega⟩)))
    · exact Or.inr (Or.inl ⟨by omega, by have := hF1.1; omega⟩)) (fun a h1 h2 => by
      rcases h1 with h1 | h1
      · exact hF1.getMem_below_next (by omega) h1 h2
      · exact hF1.getMem_above (by omega) h1 h2)
  have kp : ∀ b : Word, (b.toNat < (env.next M).toNat ∨ top.toNat - 144 ≤ b.toNat) →
      (b.toNat < (Src + 40#64).toNat ∨ (Src + 40#64).toNat + 40 * (n - j) ≤ b.toNat) → m1.getMem b = M.getMem b :=
    fun b h1 h2 => k1 b h1 fun ho => by have := hin b ho; omega
  have a8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
  have a16 : (regs .x10 + 16#64).toNat = (regs .x10).toNat + 16 := toNat_add_ofNat (by omega)
  have hhdr : ∀ b : Word, (regs .x10).toNat ≤ b.toNat → b.toNat < (regs .x10).toNat + 24 → m1.getMem b = M.getMem b :=
    fun b h1 h2 => kp b (by rcases hown.1 with h | h <;> omega) (by omega)
  refine ⟨m1', n1, hhdr _ (by omega) (by omega), (hhdr _ (by omega) (by omega)).trans hP,
    hhdr _ (by omega) (by omega), fun t ht htj => ?_, ?_⟩
  · have hT := hF.2
    rw [vecPtr_eq, vecLen_eq, hP, hn] at hT
    have et : (P + BitVec.ofNat 64 (40 * t)).toNat = P.toNat + 40 * t := toNat_add_ofNat (by omega)
    rcases Nat.lt_or_ge t j with htj' | htj'
    · refine vecT_keep (hT t (by omega)) n1 fun b h1 h2 => kp b (.inl ?_) (.inl ?_)
      · rw [et] at h2; omega
      · rw [et] at h2; omega
    · obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
      have hV := hT u (by omega)
      have eu : (P + BitVec.ofNat 64 (40 * u)).toNat = P.toNat + 40 * u := toNat_add_ofNat (by omega)
      have hw : ∀ o, o ≤ 16 → o % 8 = 0 →
          m1.getMem (P + BitVec.ofNat 64 (40 * (u + 1)) + BitVec.ofNat 64 o) =
            M.getMem (P + BitVec.ofNat 64 (40 * u) + BitVec.ofNat 64 o) := fun o ho ho8 => by
        refine Transcript.getMem_of_bytes ?_ ?_ fun k hk => ?_
        · rw [toNat_add_ofNat (by omega), et]; omega
        · rw [toNat_add_ofNat (by omega), eu]; omega
        · have e1 : P + BitVec.ofNat 64 (40 * (u + 1)) + BitVec.ofNat 64 o + BitVec.ofNat 64 k =
              Src + 40#64 + BitVec.ofNat 64 (40 * (u - j) + o + k) := BitVec.eq_of_toNat_eq (by
            rw [toNat_add_ofNat (by rw [toNat_add_ofNat (by omega), et]; omega), toNat_add_ofNat (by omega), et,
              toNat_add_ofNat (by omega), eD]; omega)
          have e2 : P + BitVec.ofNat 64 (40 * u) + BitVec.ofNat 64 o + BitVec.ofNat 64 k =
              Src + BitVec.ofNat 64 (40 * (u - j) + o + k) := BitVec.eq_of_toNat_eq (by
            rw [toNat_add_ofNat (by rw [toNat_add_ofNat (by omega), eu]; omega), toNat_add_ofNat (by omega), eu,
              toNat_add_ofNat (by omega), hSrc]; omega)
          rw [e1, e2]
          exact hcopy _ (by omega)
      refine CloneFormsT.vecT_copy hV (Runtime.MemsetT.InWin.sub (Or.inl ⟨hP1, by omega⟩)
        (x := P + BitVec.ofNat 64 (40 * (u + 1))) (n := 40 * (M.getMem (regs .x10)).toNat) (by omega)
        (by omega)) (by omega) n1 ?_ ?_ ?_
      · simpa using hw 0 (by omega) (by omega)
      · exact hw 8 (by omega) (by omega)
      · exact hw 16 (by omega) (by omega)
  · have hlS := vecT_lt hC
    exact vecT_keep hC n1 fun b h1 h2 => kp b (.inr (by omega)) (.inr (by omega))

set_option rv_sym.heap true in
/-- **The later terms moved one place up**, from instruction 104 (pc 208), the buffer with room: `memmove` of the
    terms from `j` to the length `n` one term up, then the new term's stores. -/
theorem move {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needM : Nat} (hnM : 144 + needM ≤ need) (hmv : MemmoveSpecT env p L.memmove.idx needM)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hA : Args env m top regs)
    (h232 : ∀ (R : Reg → Word) (M : MachineState) (P n T : Word) (j : Nat),
      R .x2 = top + 18446744073709551472#64 → R .x18 = regs .x10 → R .x23 = 1#64 → R .x24 = P → R .x25 = n →
      R .x21 = T → R .x22 = X22 → R .x26 = X26 →
      T.toNat = P.toNat + 40 * j → j ≤ n.toNat →
      MemOk env m top ret regs M → KeptOrFresh env m M (regs .x10) → VecT env M (regs .x10) 40 →
      M.getMem (regs .x10 + 8#64) = P → M.getMem (regs .x10 + 16#64) = n → n.toNat < (M.getMem (regs .x10)).toNat →
      GapT env M P n.toNat j → VecT env M (top + 18446744073709551488#64) 8 →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 232, ret, top⟩ :: rest, R, M⟩) :
    ∀ (R : Reg → Word) (M : MachineState) (n w : Word),
      R .x2 = top + 18446744073709551472#64 → R .x18 = regs .x10 → R .x23 = 1#64 → R .x25 = n →
      R .x27 = w → R .x21 = w <<< 3 → R .x8 = w <<< 5 → R .x22 = X22 → R .x26 = X26 → w.toNat ≤ n.toNat →
      MemOk env m top ret regs M → KeptOrFresh env m M (regs .x10) → FormT env M (regs .x10) →
      M.getMem (regs .x10 + 16#64) = n → n.toNat < (M.getMem (regs .x10)).toNat →
      VecT env M (top + 18446744073709551488#64) 8 →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 208, ret, top⟩ :: rest, R, M⟩ := by
  intro R M n w k2 k18 k23 k25 k27 k21 k8 k22 k26 hw hM hkf hF hn hcap hC
  have hR := And.intro k2 (And.intro k18 (And.intro k23 (And.intro k25 (And.intro k27 (And.intro k21
    (And.intro k8 (And.intro k22 k26)))))))
  clear k2 k18 k23 k25 k27 k21 k8 k22 k26
  have hlay := env.layout
  obtain ⟨hstk, hW, h16, -⟩ := id hA
  have := hW.nextAddr_ge
  have hW1 := hW.heapEnd_le
  have hcM : M.code = m.code := hM.2.2.2
  have hnM := hM.2.1.2.1
  have hnm := hM.2.1.1
  have hS : env.Static M := hM.2.2.1
  have hlt := vecT_lt hF.1
  have hnl := hF.2
  rw [vecPtr_eq, vecLen_eq, hn] at hnl
  obtain ⟨hP1, hP2, hP8⟩ := (buf_foot hF.1).resolve_left (by omega)
  have hcap63 := hF.1.2.1.2.2.2
  rw [rvCapAt_eq] at hcap63
  have e40 : (w <<< 5 + w <<< 3).toNat = 40 * w.toNat := sh40' (by omega)
  have eT : (M.getMem (regs .x10 + 8#64) + (w <<< 5 + w <<< 3)).toNat =
      (M.getMem (regs .x10 + 8#64)).toNat + 40 * w.toNat := by rw [BitVec.toNat_add, e40]; omega
  have eD : (M.getMem (regs .x10 + 8#64) + (w <<< 5 + w <<< 3) + 40#64).toNat =
      (M.getMem (regs .x10 + 8#64)).toNat + 40 * w.toNat + 40 := by rw [toNat_add_ofNat (by omega), eT]
  have eN : ((n - w) <<< 5 + (n - w) <<< 3).toNat = 40 * (n.toNat - w.toNat) := by
    rw [sh40' (by rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 hw)]; omega),
      BitVec.toNat_sub_of_le (BitVec.le_def.2 hw)]
  have hC' : True → VecT env M (top + 18446744073709551488#64) 8 := fun _ => hC
  have hF' : True → FormT env M (regs .x10) := fun _ => hF
  have hM' : True → MemOk env m top ret regs M := fun _ => hM
  have hkf' : True → KeptOrFresh env m M (regs .x10) := fun _ => hkf
  have hnl' : True → TermsT env M (M.getMem (regs .x10 + 8#64)) n.toNat := fun _ => hnl
  have hA' : True → Args env m top regs := fun _ => hA
  have wa8 : inWindow (regs .x10 + 8#64) 8 = true := inWin_word hF.1.1 (by decide) hW1 this
  have ha8 : (regs .x10).toNat % 8 = 0 := hF.1.2.1.2.1
  have a8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
  have e144 := CloneFormsT.es (top := top) (c := 18446744073709551472#64) (k := 144) rfl (by omega)
  have e128 := CloneFormsT.es (top := top) (c := 18446744073709551488#64) (k := 128) rfl (by omega)
  clear hC hF hM hkf hnl hA
  rv_introT hR
  rv_symT hp stop [232] with [hL] using [hmv]
  · exact wa8
  · -- no later terms: `j = n`
    rw [BitVec.le_def] at hc
    exact h232 _ _ _ n _ w.toNat rfl rfl rfl rfl rfl rfl rfl rfl eT hw (hM' trivial) (hkf' trivial) (hF' trivial).1 rfl
      hn hcap (fun t ht htj => hnl' trivial t (by omega)) (hC' trivial)
  · exact fun h => absurd h (by decide)
  · rw [BitVec.lt_def] at hc
    right
    unfold OffStack
    rw [inWindow_iff, eD, eN, eT]
    omega
  · -- after the move
    rw [BitVec.lt_def] at hc
    have hwn : w.toNat < n.toNat := by omega
    obtain ⟨hm1, n1, g0, g8, g16, hgap, hC1⟩ := move_mem (Src := M.getMem (regs .x10 + 8#64) + (w <<< 5 + w <<< 3))
      (j := w.toNat) (n := n.toNat) hstk (hA' trivial) (hM' trivial) (hkf' trivial) (hF' trivial) rfl (by rw [hn])
      hcap hwn eT (by rw [e128]; omega) (hC' trivial) hret1_14
      (fun b hb => by
        have h : DwordsOf (M.getMem (regs .x10 + 8#64) + (w <<< 5 + w <<< 3) + 40#64)
          ((n - w) <<< 5 + (n - w) <<< 3).toNat b := hb
        rwa [eN] at h) hret1_15 hret1_19 (by rw [← eN]; exact hret1_17)
    have hkf1 : KeptOrFresh env m m1 (regs .x10) := by
      have ep : vecPtr m1 (regs .x10) = vecPtr M (regs .x10) := g8
      have ec : vecCap m1 (regs .x10) = vecCap M (regs .x10) := by rw [vecCap_eq, vecCap_eq]; exact g0
      unfold KeptOrFresh; rw [ep, ec]; exact hkf' trivial
    have hV1 : VecT env m1 (regs .x10) 40 := by
      obtain ⟨w1, w2, w3⟩ := (hF' trivial).1
      refine ⟨w1, w2.keep (by rw [rvCapAt_eq]; exact g0) (by rw [rvPtrAt_eq]; exact g8) n1, ?_⟩
      rw [vecLen_eq, vecCap_eq, g16, g0]; rwa [vecLen_eq, vecCap_eq] at w3
    exact h232 _ _ _ n _ w.toNat rfl rfl rfl rfl rfl rfl rfl rfl eT hw hm1 hkf1 hV1 g8 (g16.trans hn)
      (by rw [g0]; exact hcap) hgap hC1

/-- **After the clone and the product**: `clone` writing at most its header at `S = top - 128`, `E::mul` nothing:
    `MemOk`, `self` (its header and terms) and the clone kept. -/
theorem after_cm {m M m1 m2 : MachineState} {top ret : Word} {regs : Reg → Word} {out1 : Word → Prop}
    (hlim : env.stackLimit.toNat + 144 ≤ top.toNat) (hA : Args env m top regs) (hM : MemOk env m top ret regs M)
    (hkf : KeptOrFresh env m M (regs .x10)) (hF : FormT env M (regs .x10))
    (hF1 : env.Frame (top + 18446744073709551472#64) out1 M m1)
    (hout1 : ∀ b, out1 b → InRange (top + 18446744073709551488#64) 24 b) (hS1 : env.Static m1)
    (hc1 : m1.code = M.code) (hC : VecT env m1 (top + 18446744073709551488#64) 8)
    (hF2 : env.Frame (top + 18446744073709551472#64) (fun _ => False) m1 m2) (hS2 : env.Static m2)
    (hc2 : m2.code = m1.code) :
    MemOk env m top ret regs m2 ∧ (env.next M).toNat ≤ (env.next m2).toNat ∧ KeptOrFresh env m m2 (regs .x10) ∧
      FormT env m2 (regs .x10) ∧ m2.getMem (regs .x10) = M.getMem (regs .x10) ∧
      m2.getMem (regs .x10 + 8#64) = M.getMem (regs .x10 + 8#64) ∧
      m2.getMem (regs .x10 + 16#64) = M.getMem (regs .x10 + 16#64) ∧ VecT env m2 (top + 18446744073709551488#64) 8 := by
  have hlay := env.layout
  obtain ⟨-, hW, -, hx2, -, hown, -, -, -, -⟩ := id hA
  rw [hx2] at hown
  have hnm := hM.2.1.1
  have hnM := hM.2.1.2.1
  have e144 := CloneFormsT.es (top := top) (c := 18446744073709551472#64) (k := 144) rfl (by omega)
  have e128 := CloneFormsT.es (top := top) (c := 18446744073709551488#64) (k := 128) rfl (by omega)
  have hin1 : ∀ b, out1 b → top.toNat - 128 ≤ b.toNat ∧ b.toNat < top.toNat - 104 := fun b hb => by
    have h := hout1 b hb; unfold InRange at h; omega
  obtain ⟨m1', n1, k1⟩ := call_keep hlim hM hF1 hS1 hc1 (fun b hb => by
      have := hin1 b hb; exact ⟨.inl ⟨by omega, by omega⟩, .inl (by omega)⟩) (fun a h1 h2 => by
      rcases h1 with h1 | h1
      · exact hF1.getMem_below_next hnM h1 h2
      · exact hF1.getMem_above (by omega) h1 h2)
  obtain ⟨m2', n2, k2⟩ := call_keep hlim m1' hF2 hS2 hc2 (fun b hb => hb.elim) (fun a h1 h2 => by
      rcases h1 with h1 | h1
      · exact hF2.getMem_below_next hF1.2.1 h1 h2
      · exact hF2.getMem_above (by omega) h1 h2)
  have kp : ∀ b : Word, (b.toNat < (env.next M).toNat ∨ top.toNat ≤ b.toNat) → m2.getMem b = M.getMem b :=
    fun b h => by
      rw [k2 b (by omega) id, k1 b (by omega) fun ho => by have := hin1 b ho; omega]
  have hlt := vecT_lt hF.1
  have hhdr : ∀ b : Word, (regs .x10).toNat ≤ b.toNat → b.toNat < (regs .x10).toNat + 24 → m2.getMem b = M.getMem b :=
    fun b h1 h2 => kp b (by rcases hown.1 with h | h <;> omega)
  have hF2' : FormT env m2 (regs .x10) := hF.keep (by omega) hhdr fun b h1 h2 => kp b (.inl (by
    rcases hF.foot with h | ⟨-, h3, -⟩
    · omega
    · omega))
  have a8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
  have a16 : (regs .x10 + 16#64).toNat = (regs .x10).toNat + 16 := toNat_add_ofNat (by omega)
  have g0 := hhdr (regs .x10) (by omega) (by omega)
  have g8 := hhdr (regs .x10 + 8#64) (by omega) (by omega)
  have g16 := hhdr (regs .x10 + 16#64) (by omega) (by omega)
  refine ⟨m2', by omega, ?_, hF2', g0, g8, g16, ?_⟩
  · have ep : vecPtr m2 (regs .x10) = vecPtr M (regs .x10) := g8
    have ec : vecCap m2 (regs .x10) = vecCap M (regs .x10) := by rw [vecCap_eq, vecCap_eq]; exact g0
    unfold KeptOrFresh; rw [ep, ec]; exact hkf
  · exact vecT_keep hC n2 fun b h1 _ => k2 b (.inr (by omega)) id

/-- **After `grow_one`**, `self`'s buffer full: the header's two words written, a fresh buffer with the terms'
    bytes: `MemOk`, `self` a `Form` with room, the clone kept. -/
theorem after_grow {m M m3 : MachineState} {top ret n : Word} {regs : Reg → Word} {out3 : Word → Prop}
    (hlim : env.stackLimit.toNat + 144 ≤ top.toNat) (hA : Args env m top regs) (hM : MemOk env m top ret regs M)
    (hF : FormT env M (regs .x10)) (hn : M.getMem (regs .x10 + 16#64) = n) (hcap : n = M.getMem (regs .x10))
    (hC : VecT env M (top + 18446744073709551488#64) 8)
    (hF3 : env.Frame (top + 18446744073709551472#64) out3 M m3)
    (hout3 : ∀ b, out3 b → b = regs .x10 ∨ b = regs .x10 + 8#64) (hS3 : env.Static m3) (hc3 : m3.code = M.code)
    (hg1 : (M.getMem (regs .x10)).toNat + 1 ≤ (m3.getMem (regs .x10)).toNat)
    (hg2 : env.Fresh M m3 (m3.getMem (regs .x10 + 8#64)) ((m3.getMem (regs .x10)).toNat * 40))
    (hg3 : ∀ k < (M.getMem (regs .x10)).toNat * 40, m3.getByte (m3.getMem (regs .x10 + 8#64) + BitVec.ofNat 64 k) =
      M.getByte (M.getMem (regs .x10 + 8#64) + BitVec.ofNat 64 k))
    (hRV : RawVecT env m3 (regs .x10) 40) :
    MemOk env m top ret regs m3 ∧ KeptOrFresh env m m3 (regs .x10) ∧ FormT env m3 (regs .x10) ∧
      m3.getMem (regs .x10 + 16#64) = n ∧ n.toNat < (m3.getMem (regs .x10)).toNat ∧
      VecT env m3 (top + 18446744073709551488#64) 8 := by
  have hlay := env.layout
  obtain ⟨-, hW, -, hx2, -, hown, -, -, -, -⟩ := id hA
  rw [hx2] at hown
  have hnm := hM.2.1.1
  have hnM := hM.2.1.2.1
  have hge := hW.next_ge
  have hlt := vecT_lt hF.1
  have e128 := CloneFormsT.es (top := top) (c := 18446744073709551488#64) (k := 128) rfl (by omega)
  have e144 := CloneFormsT.es (top := top) (c := 18446744073709551472#64) (k := 144) rfl (by omega)
  have hcn : n.toNat = (M.getMem (regs .x10)).toNat := by rw [hcap]
  have a8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
  have a16 : (regs .x10 + 16#64).toNat = (regs .x10).toNat + 16 := toNat_add_ofNat (by omega)
  have hin3 : ∀ b, out3 b → (regs .x10).toNat ≤ b.toNat ∧ b.toNat < (regs .x10).toNat + 16 := fun b hb => by
    rcases hout3 b hb with h | h <;> rw [h] <;> omega
  obtain ⟨m3', n3, k3⟩ := call_keep hlim hM hF3 hS3 hc3 (fun b hb => by
      have := hin3 b hb
      exact ⟨Or.inr (Or.inr (Or.inr (.inl ⟨by omega, by omega⟩))), by rcases hown.1 with h | h <;> omega⟩)
    (fun a h1 h2 => by
      rcases h1 with h1 | h1
      · exact hF3.getMem_below_next (by omega) h1 h2
      · exact hF3.getMem_above (by omega) h1 h2)
  have g16 : m3.getMem (regs .x10 + 16#64) = n :=
    (k3 _ (by rcases hown.1 with h | h <;> omega) fun ho => by have := hin3 _ ho; omega).trans hn
  have hl := hF.1.2.2
  rw [vecLen_eq, vecCap_eq, hn, ← hcap] at hl
  have hterms := hF.2
  rw [vecPtr_eq, vecLen_eq, hn] at hterms
  obtain ⟨hf1, hf2⟩ := hg2
  have hnm3 := hM.2.1.1.trans (hF3.1)
  have hP3 : (m3.getMem (regs .x10 + 8#64)).toNat % 8 = 0 := by
    have h := hRV.2.2.1
    rw [rvCapAt_eq, rvPtrAt_eq] at h
    rcases h with h | ⟨-, -, h⟩
    · omega
    · exact h
  have hnx3 := m3'.2.1.2.1
  refine ⟨m3', .inr (by rw [vecPtr_eq]; omega), ⟨⟨hF.1.1, hRV, by rw [vecLen_eq, vecCap_eq, g16]; omega⟩, ?_⟩,
    g16, by omega, ?_⟩
  · rw [vecPtr_eq, vecLen_eq, g16]
    intro t ht
    have hV := hterms t ht
    have hP := hF.foot
    rw [vecLen_eq, vecPtr_eq, hn] at hP
    obtain ⟨hP1, hP2, hP8⟩ := hP.resolve_left (by omega)
    have et : (M.getMem (regs .x10 + 8#64) + BitVec.ofNat 64 (40 * t)).toNat =
        (M.getMem (regs .x10 + 8#64)).toNat + 40 * t := toNat_add_ofNat (by omega)
    have et3 : (m3.getMem (regs .x10 + 8#64) + BitVec.ofNat 64 (40 * t)).toNat =
        (m3.getMem (regs .x10 + 8#64)).toNat + 40 * t := toNat_add_ofNat (by omega)
    have hw : ∀ o, o ≤ 16 → o % 8 = 0 →
        m3.getMem (m3.getMem (regs .x10 + 8#64) + BitVec.ofNat 64 (40 * t) + BitVec.ofNat 64 o) =
          M.getMem (M.getMem (regs .x10 + 8#64) + BitVec.ofNat 64 (40 * t) + BitVec.ofNat 64 o) := fun o ho ho8 => by
      refine Transcript.getMem_of_bytes ?_ ?_ fun k hk => ?_
      · rw [toNat_add_ofNat (by omega), et3]; omega
      · rw [toNat_add_ofNat (by omega), et]; omega
      · rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add,
          ← BitVec.ofNat_add]
        exact hg3 _ (by omega)
    refine CloneFormsT.vecT_copy hV (Or.inl ⟨by omega, by omega⟩) (by omega) (by omega) ?_ ?_ ?_
    · simpa using hw 0 (by omega) (by omega)
    · exact hw 8 (by omega) (by omega)
    · exact hw 16 (by omega) (by omega)
  · have hlS := vecT_lt hC
    exact vecT_keep hC (by omega) fun b h1 _ => k3 b (.inr (by omega)) fun ho => by
      have := hin3 b ho; rcases hown.1 with h | h <;> omega

/-! ## The insertion: the monomial cloned, the coefficient weighted, the buffer grown -/

set_option rv_sym.heap true in
/-- **The insertion**, from instruction 87 (pc 174), `other`'s term `o`'s monomial's length in `x12`: its clone at
    `top - 128`, the weighted coefficient, the buffer grown when full, then the move. -/
theorem ins {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needC needE needG : Nat} (hnC : 144 + needC ≤ need) (hnE : 144 + needE ≤ need)
    (hnG : 144 + needG ≤ need) (hcl : CloneSpecT env 8 p L.clone.idx needC)
    (hmul : Field.EMulT.specT env p L.mul.idx needE) (hgo : GrowOneSpecT env 8 40 p L.growOne.idx needG)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hA : Args env m top regs) {X22 X26 : Word}
    (h208 : ∀ (R : Reg → Word) (M : MachineState) (n w : Word),
      R .x2 = top + 18446744073709551472#64 → R .x18 = regs .x10 → R .x23 = 1#64 → R .x25 = n →
      R .x27 = w → R .x21 = w <<< 3 → R .x8 = w <<< 5 → R .x22 = X22 → R .x26 = X26 → w.toNat ≤ n.toNat →
      MemOk env m top ret regs M → KeptOrFresh env m M (regs .x10) → FormT env M (regs .x10) →
      M.getMem (regs .x10 + 16#64) = n → n.toNat < (M.getMem (regs .x10)).toNat →
      VecT env M (top + 18446744073709551488#64) 8 →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 208, ret, top⟩ :: rest, R, M⟩) :
    ∀ (R : Reg → Word) (M : MachineState) (o n w : Word),
      R .x2 = top + 18446744073709551472#64 → R .x18 = regs .x10 → R .x19 = o → R .x23 = 1#64 → R .x25 = n →
      R .x27 = w → R .x21 = w <<< 3 → R .x8 = w <<< 5 → R .x22 = X22 → R .x26 = X26 → R .x12 = M.getMem (o + 16#64) →
      w.toNat ≤ n.toNat → MemOk env m top ret regs M → KeptOrFresh env m M (regs .x10) → FormT env M (regs .x10) →
      M.getMem (regs .x10 + 16#64) = n → VecT env M o 8 → InWin env o 40 →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 174, ret, top⟩ :: rest, R, M⟩ := by
  intro R M o n w k2 k18 k19 k23 k25 k27 k21 k8 k22 k26 k12 hw hM hkf hF hn ho hoW
  have hR := And.intro k2 (And.intro k18 (And.intro k19 (And.intro k23 (And.intro k25 (And.intro k27 (And.intro k21
    (And.intro k8 (And.intro k22 (And.intro k26 k12)))))))))
  clear k2 k18 k19 k23 k25 k27 k21 k8 k22 k26 k12
  have hlay := env.layout
  obtain ⟨hstk, hW, h16, -⟩ := id hA
  have := hW.nextAddr_ge
  have hW1 := hW.heapEnd_le
  have hcM : M.code = m.code := hM.2.2.2
  have hnM := hM.2.1.2.1
  have hnm := hM.2.1.1
  have hS : env.Static M := hM.2.2.1
  have hbo := (vecT_buf ho).1
  rw [vecLen_eq, vecPtr_eq] at hbo
  have hlo := vecT_lt ho
  have hlt := vecT_lt hF.1
  have wo8 : inWindow (o + 8#64) 8 = true := inWin_word ho.1 (by decide) hW1 this
  have wo16 : inWindow (o + 16#64) 8 = true := inWin_word ho.1 (by decide) hW1 this
  have wo24 : inWindow (o + 24#64) 8 = true := inWin_word hoW (by decide) hW1 this
  have wo32 : inWindow (o + 32#64) 8 = true := inWin_word hoW (by decide) hW1 this
  have wa0 : inWindow (regs .x10) 8 = true := by simpa using inWin_word (k := 0) hF.1.1 (by decide) hW1 this
  have hao := ho.2.1.2.1
  have haa := hF.1.2.1.2.1
  have hM' : True → MemOk env m top ret regs M := fun _ => hM
  have hkf' : True → KeptOrFresh env m M (regs .x10) := fun _ => hkf
  have hF' : True → FormT env M (regs .x10) := fun _ => hF
  have ho' : True → VecT env M o 8 := fun _ => ho
  have hA' : True → Args env m top regs := fun _ => hA
  clear hM hkf hF ho hA
  rv_introT hR
  rv_symT hp stop [208] with [hL] using [hcl, hmul, hgo]
  · exact wa0
  all_goals
    obtain ⟨hm2, n2, hkf2, hF2, g0, g8, g16, hC2⟩ := after_cm hstk (hA' trivial) (hM' trivial) (hkf' trivial)
      (hF' trivial) hret1_14 (fun b hb => hb) hret1_15 hret1_24
      ⟨hret1_16, ⟨hret1_17, hret1_18, hret1_19, hret1_20⟩, hret1_21⟩ hret2_14 hret2_15 hret2_18
    have hRV2 := hF2.1.2.1
    have hl2 := hF2.1.2.2
    rw [vecLen_eq, vecCap_eq, g16, hn, g0] at hl2
  · -- room: no growth
    have hne : n.toNat ≠ (M.getMem (regs .x10)).toNat := fun h => hc (BitVec.eq_of_toNat_eq (by rw [h, g0]))
    exact h208 _ _ n w rfl rfl rfl rfl rfl rfl rfl rfl rfl hw hm2 hkf2 hF2 (g16.trans hn) (by rw [g0]; omega) hC2
  · obtain ⟨-, -, -, hx2, -, hown, -⟩ := hA' trivial
    rw [hx2] at hown
    have e144 := CloneFormsT.es (top := top) (c := 18446744073709551472#64) (k := 144) rfl (by omega)
    simp only [Layouts.RawVecInner.byteSize]
    rcases hown.1 with h | h <;> omega
  · exact hRV2.2.2.1.live
  · exact hRV2.2.2.2
  · exact hRV2.1
  · exact hRV2.2.2.1
  · exact hRV2.2.2.2
  · -- full: after `grow_one`
    rw [rvCapAt_eq] at hret3_16 hret3_17 hret3_18
    obtain ⟨hm3, hkf3, hF3, g16', hlt3, hC3⟩ := after_grow hstk (hA' trivial) hm2 hF2 (g16.trans hn)
      hc hC2 hret3_14 (fun b hb => by
        rcases hb with h | h
        · exact .inl (by rw [h, rvCapAt_eq]; rfl)
        · exact .inr h) hret3_15 hret3_23 hret3_16 hret3_17 hret3_18
      ⟨hret3_19, hret3_20, hret3_21, hret3_22⟩
    exact h208 _ _ n w rfl rfl rfl rfl rfl rfl rfl rfl rfl hw hm3 hkf3 hF3 g16' hlt3 hC3

/-! ## The return -/

set_option rv_sym.heap true in
/-- **The return**, from instruction 162 (pc 324): the saved registers reloaded. -/
theorem exit {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) OutT ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩) (hA : Args env m top regs) :
    ∀ R M, R .x2 = top + 18446744073709551472#64 → MemOk env m top ret regs M → FormT env M (regs .x10) →
      KeptOrFresh env m M (regs .x10) → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 324, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hR hM hF hkf
  have hlay := env.layout
  obtain ⟨hstk, hW, h16, -⟩ := hA
  obtain ⟨⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13⟩, hF0, hS0, hc0⟩ := hM
  have := hW.nextAddr_ge
  rv_introT hR
  rv_symT hp
  · have h := hF.1.2.2
    rwa [vecLen_eq, vecCap_eq] at h
  · exact hF.2
  · rw [← vecPtr_eq, ← vecPtr_eq, ← vecCap_eq, ← vecCap_eq]; exact hkf

/-! ## The new term's stores -/

/-- **The outer loop's head** (25, pc 50) with `k + 1` of `other`'s terms left, from term `t` (`x19`). -/
def OInv (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551472#64 ∧ R .x18 = regs .x10 ∧ R .x23 = 1#64 ∧ R .x24 = M.getMem (regs .x10 + 8#64) ∧
    (R .x22).toNat = (regs .x11).toNat + 40 * (regs .x12).toNat ∧
    ∃ t, t + k + 1 = (regs .x12).toNat ∧ (R .x19).toNat = (regs .x11).toNat + 40 * t ∧
      MemOk env m top ret regs M ∧ FormT env M (regs .x10) ∧ KeptOrFresh env m M (regs .x10)

set_option rv_sym.heap true in
/-- **The new term's stores**, from instruction 116 (pc 232): the clone's header and the weighted coefficient at
    `T = P + 40 j`, the length one more, then the next of `other`'s terms (25) or the return. -/
theorem store {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) OutT ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩) (hA : Args env m top regs) {k t : Nat}
    (h50 : 0 < k → ∀ R M, OInv env m top ret regs (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 50, ret, top⟩ :: rest, R, M⟩) :
    ∀ (R : Reg → Word) (M : MachineState) (P n T : Word) (j : Nat),
      R .x2 = top + 18446744073709551472#64 → R .x18 = regs .x10 → R .x23 = 1#64 → R .x24 = P → R .x25 = n →
      R .x21 = T → (R .x22).toNat = (regs .x11).toNat + 40 * (regs .x12).toNat →
      (R .x26).toNat = (regs .x11).toNat + 40 * (t + 1) → t + k + 1 = (regs .x12).toNat →
      T.toNat = P.toNat + 40 * j → j ≤ n.toNat →
      MemOk env m top ret regs M → KeptOrFresh env m M (regs .x10) → VecT env M (regs .x10) 40 →
      M.getMem (regs .x10 + 8#64) = P → M.getMem (regs .x10 + 16#64) = n → n.toNat < (M.getMem (regs .x10)).toNat →
      GapT env M P n.toNat j → VecT env M (top + 18446744073709551488#64) 8 →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 232, ret, top⟩ :: rest, R, M⟩ := by
  intro R M P n T j k2 k18 k23 k24 k25 k21 h22 h26 htk hT hj hM hkf hV hP hn hcap hgap hC
  have hR := And.intro k2 (And.intro k18 (And.intro k23 (And.intro k24 (And.intro k25 k21))))
  clear k2 k18 k23 k24 k25 k21
  have hlay := env.layout
  obtain ⟨hstk, hW, h16, hpre⟩ := id hA
  have := hW.nextAddr_ge
  have hW1 := hW.heapEnd_le
  have hcM : M.code = m.code := hM.2.2.2
  have hnM := hM.2.1.2.1
  have hnm := hM.2.1.1
  obtain ⟨-, -, hbuf, hcap63⟩ := hV.2.1
  rw [rvCapAt_eq, rvPtrAt_eq, hP] at hbuf
  rw [rvCapAt_eq] at hcap63
  obtain ⟨hP1, hP2, hP8⟩ : 0x10000000 ≤ P.toNat ∧ P.toNat + 40 * (M.getMem (regs .x10)).toNat ≤ (env.next M).toNat ∧
      P.toNat % 8 = 0 := by
    rcases hbuf with h | ⟨h1, h2, h3⟩
    · omega
    · unfold Env.Live at h2; exact ⟨h1, by omega, h3⟩
  have e8 : (T + 8#64).toNat = T.toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (T + 16#64).toNat = T.toNat + 16 := toNat_add_ofNat (by omega)
  have e24 : (T + 24#64).toNat = T.toNat + 24 := toNat_add_ofNat (by omega)
  have e32 : (T + 32#64).toNat = T.toNat + 32 := toNat_add_ofNat (by omega)
  have wa16 : inWindow (regs .x10 + 16#64) 8 = true := inWin_word hV.1 (by decide) hW1 this
  have ha8 : (regs .x10).toNat % 8 = 0 := hV.2.1.2.1
  have hlt := vecT_lt hV
  have a16 : (regs .x10 + 16#64).toNat = (regs .x10).toNat + 16 := toNat_add_ofNat (by omega)
  have s8 : top + 18446744073709551488#64 + 8#64 = top + 18446744073709551496#64 := by rw [BitVec.add_assoc]; rfl
  have s16 : top + 18446744073709551488#64 + 16#64 = top + 18446744073709551504#64 := by rw [BitVec.add_assoc]; rfl
  have htm := term_mem (S := top + 18446744073709551488#64) (v3 := R .x19) (v4 := R .x20) hstk hA hM hkf hV hP
    hcap hT hj hgap hC
  rw [s8, s16] at htm
  obtain ⟨m6, n6, g8, hF6, hkf6⟩ := htm
  have hex := exit hp hk hA
  have e1 : (n + 1#64).toNat = n.toNat + 1 := toNat_add_ofNat (by omega)
  clear hV hgap hC hM hkf hbuf hpre hA hk
  rv_introT hR
  rv_symT hp stop [50, 324]
  · have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h26, h22]; omega)) hc
      · exact h
    clear hc
    exact h50 hk0 _ _ ⟨rfl, rfl, rfl, g8.symm, h22, t + 1, by omega, h26, m6, hF6, hkf6⟩
  · exact hex _ _ rfl m6 hF6 hkf6

end Rv64mc.Proof.Layout.AddScaledT
