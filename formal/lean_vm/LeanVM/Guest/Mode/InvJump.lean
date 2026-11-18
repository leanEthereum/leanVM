module

public import LeanVM.Guest.Mode.InvStep
public import LeanVM.Guest.CoreMode.Spec

/-!
# The stack after a step

What each step does to the stack (`StackAt`), for any frame predicate `Q` and contracts `Ct`: one in the frame (a
fall-through, a forward or table jump, `stack_move`) moves the top activation's offset; a return
(`ret_stack`) pops it, the caller's frame predicate holding again (`Resume`) from what the callee
guarantees (`PostAt`) at its first frame, rebuilt down its loop's iterations (`Chain.back`); a loop's tail call
(`tail_stack`) adds an iteration; a call (`call_stack`) pushes the callee's activation, the caller
suspended; `main`'s halting jump ends the run (`halt_of`).
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

variable {Ct : Cts} {Q : Cert → ℕ → St → Prop}

/-- `main`'s activation is at the bottom, in frame `0`. -/
theorem Below.main_fp {Ks : List Cert} {Km : Cert} {m : Mem} {a : Act} {rest : List Act}
    (h : Below Ct Q Ks Km m a rest) (hm : a.K.F.main = true) : a.fp = 0 := by
  rcases rest with _ | ⟨b, rest⟩
  · exact h.2.2
  · exact absurd hm (by rw [h.1]; decide)

/-- **A step in the frame**: the top activation at another offset. -/
theorem stack_move {Ks : List Cert} {Km : Cert} {s s' : St} {a : Act} {rest : List Act}
    (ha : ActOk Ct Ks s.mem a) (hfpa : a.fp = s.fp) (hbel : Below Ct Q Ks Km s.mem a rest)
    (hle : s.mem ≤ s'.mem) (hfp : s'.fp = s.fp) {j : ℕ} (hj : j < a.K.code.length)
    (hpc : s'.pc = a.K.F.entry + j) (hat : Q a.K j s') : StackAt Ct Q Ks Km s' :=
  ⟨a, rest, j, ha.mono hle, hfpa.trans hfp.symm, hj, hpc, hat, hbel.mono hle⟩

/-- **`main`'s halting jump** goes to the final state. -/
theorem halt_of {prog : LeanIsaProgram} {C : Ctx} {Ks : List Cert} {Km : Cert} {E0 : Env}
    (P : ProgOk prog C Ks Km E0) {K : Cert} (hK : K ∈ Ks) {s' : St} (hpc : s'.pc = K.E.halt)
    (hfp : s'.fp = 0) : Halted prog { s' with steps := s'.steps + 1 } :=
  halted_of (hpc.trans ((P.env K hK).2.2.2.2.trans P.halt)) hfp

/-- The program's halting pc is below `2^30`. -/
theorem halt_lt {prog : LeanIsaProgram} {C : Ctx} {Ks : List Cert} {Km : Cert} {E0 : Env}
    (P : ProgOk prog C Ks Km E0) {K : Cert} (hK : K ∈ Ks) : K.E.halt < 2 ^ 30 := by
  have hl : 2 ^ prog.logSize ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) prog.logSize_le
  have h1 : 1 ≤ 2 ^ prog.logSize := Nat.one_le_two_pow
  rw [(P.env K hK).2.2.2.2.trans P.halt]
  omega

/-! ## A return -/

/-- **A return pops the activation**: its header names the caller's return point and frame, where the
caller's frame predicate holds again from what the callee guarantees at its first frame, rebuilt down
its loop's iterations. -/
theorem ret_stack {prog : LeanIsaProgram} {C : Ctx} {Ks : List Cert} {Km : Cert} {E0 : Env}
    (P : ProgOk prog C Ks Km E0) (hsz : C.ops.size ≤ 2 ^ 30) {M : ℕ → E} {s s1 s' : St} {a : Act}
    {rest : List Act} (ha : ActOk Ct Ks s.mem a) (hfpa : a.fp = s1.fp)
    (hbel : Below Ct Q Ks Km s.mem a rest) (hnot : a.K ≠ Km) (hle1 : s.mem ≤ s1.mem)
    (hmono : ∀ K ∈ Ks, ∀ {i : ℕ} {s s' : St}, s.mem ≤ s'.mem → s'.fp = s.fp → Q K i s → Q K i s')
    (hRA : PostAt Ct a.K.F.entry a.K.F.sig s1.mem s1.fp) (hf' : Fine M s') (hle' : s1.mem ≤ s'.mem)
    (hpcs : s'.pc < 2 ^ 62) (hvd : s1.mem.get (s1.fp + 0) = some (ofK (g ^ s'.pc)))
    (hvf : s1.mem.get (s1.fp + 1) = some (ofK (g ^ s'.fp))) :
    StackAt Ct Q Ks Km { s' with steps := s'.steps + 1 } := by
  rcases rest with _ | ⟨b, rest⟩
  · exact absurd hbel.1 hnot
  obtain ⟨-, r, h0, h1, ⟨ro, m0, hr, hro, hm0, hres⟩, hb, hbel'⟩ := hbel
  have hrlt : r < 2 ^ 62 := by have := code_pc (P.ok b.K hb.mem) hro; omega
  have h0' : s1.mem.get (s1.fp + 0) = some (ofK (g ^ r)) := by rw [← hfpa]; exact hle1.get _ _ h0
  have h1' : s1.mem.get (s1.fp + 1) = some (ofK (g ^ b.fp)) := by rw [← hfpa]; exact hle1.get _ _ h1
  obtain ⟨hpc', hfp'⟩ := ret_regs hrlt hb.fp h0' h1' hpcs hf'.fp hvd hvf
  have hle : s.mem ≤ s'.mem := Mem.le_trans hle1 hle'
  have hch := ha.chain.mono hle
  have hP0 := hch.back hf'.agree.wf hf'.agree.used (hfpa ▸ hRA.mono hle')
  have hT0 := hch.term (ha.term.mono hle)
  have hat := hres s'.mem (Mem.le_trans hm0 hle) hf'.agree.wf hf'.agree.used (hch.fp0 ha.fp) hb.fp
    hP0 hT0
  exact ⟨b, rest, ro, hb.mono hle, hfp'.symm, hro, by rw [show s'.pc = r from hpc', hr],
    hmono b.K hb.mem (s := stOf s'.mem b.fp) (Mem.le_refl _) hfp' hat, hbel'.mono hle⟩

/-! ## A tail call -/

/-- **A loop's tail call adds an iteration**: the next frame at the function's entry, its header
copied from this frame's, this frame kept, returning what the next one does. -/
theorem tail_stack {Ks : List Cert} {Km : Cert} {M : ℕ → E} {s s1 s' : St} {a : Act}
    {rest : List Act} (ha : ActOk Ct Ks s.mem a) (hfpa : a.fp = s1.fp)
    (hbel : Below Ct Q Ks Km s.mem a rest) (hle1 : s.mem ≤ s1.mem) (hfp1 : s1.fp < maxCells)
    (hf' : Fine M s') (hle' : s1.mem ≤ s'.mem) (hKm : Km.F.main = true) (hne : 0 < a.K.code.length)
    (hmain : a.K.F.main = false)
    (hpc' : s'.pc = a.K.F.entry) (hTE : TermAt s'.mem s'.fp a.K.F.sig)
    (hhdr : ∀ o < 2, ∃ u, s'.mem.get (s1.fp + o) = some u ∧ s'.mem.get (s'.fp + o) = some u)
    (hback : Back Ct a.K.F.entry a.K.F.sig s'.mem s1.fp s'.fp) (hat : Q a.K 0 { s' with steps := s'.steps + 1 }) :
    StackAt Ct Q Ks Km { s' with steps := s'.steps + 1 } := by
  have hle : s.mem ≤ s'.mem := Mem.le_trans hle1 hle'
  rcases rest with _ | ⟨b, rest⟩
  · rw [hbel.1, hKm] at hmain
    cases hmain
  obtain ⟨-, r, h0, h1, hsp, hb, hbel'⟩ := hbel
  obtain ⟨u0, hu0, hu0'⟩ := hhdr 0 (by omega)
  obtain ⟨u1, hu1, hu1'⟩ := hhdr 1 (by omega)
  have e0 : u0 = ofK (g ^ r) := Option.some.inj (hu0.symm.trans (by rw [← hfpa]; exact hle.get _ _ h0))
  have e1 : u1 = ofK (g ^ b.fp) :=
    Option.some.inj (hu1.symm.trans (by rw [← hfpa]; exact hle.get _ _ h1))
  have hit : IterOk Ct s'.mem a.K ⟨s1.fp⟩ s'.fp := ⟨hfp1, hfpa ▸ ha.term.mono hle, hback, hf'.fp⟩
  exact ⟨⟨a.K, ⟨s1.fp⟩ :: a.its, s'.fp, a.fp0⟩, b :: rest, 0,
    ⟨ha.mem, ⟨hit, hfpa ▸ ha.chain.mono hle⟩, hTE, hf'.fp⟩, rfl, hne, by simp [hpc'],
    hat, hmain, r, e0 ▸ hu0', e1 ▸ hu1', hsp.mono hle, hb.mono hle, hbel'.mono hle⟩

/-! ## A call -/

/-- **A call pushes the callee's activation**, at its entry, its header naming the caller's return
point and frame, the caller suspended. -/
theorem call_stack {Ks : List Cert} {Km : Cert} {M : ℕ → E} {s s1 s' : St} {a : Act}
    {rest : List Act} {K' : Cert} {ro : ℕ} (ha : ActOk Ct Ks s.mem a) (hfpa : a.fp = s1.fp)
    (hbel : Below Ct Q Ks Km s.mem a rest) (hle1 : s.mem ≤ s1.mem) (hf' : Fine M s')
    (hle' : s1.mem ≤ s'.mem) (hK' : K' ∈ Ks) (hne : 0 < K'.code.length) (hent : K'.F.entry = s'.pc)
    (hmain' : K'.F.main = false) (hro : ro < a.K.code.length)
    (hd0 : s'.mem.get (s'.fp + 0) = some (ofK (g ^ (a.K.F.entry + ro))))
    (hd1 : s'.mem.get (s'.fp + 1) = some (ofK (g ^ s1.fp))) (hTE : TermAt s'.mem s'.fp K'.F.sig)
    (hat : Q K' 0 { s' with steps := s'.steps + 1 })
    (hres : Resume Ct (Q a.K) s1.fp ro K'.F.entry K'.F.sig s'.fp s'.mem) :
    StackAt Ct Q Ks Km { s' with steps := s'.steps + 1 } := by
  have hle : s.mem ≤ s'.mem := Mem.le_trans hle1 hle'
  exact ⟨⟨K', [], s'.fp, s'.fp⟩, a :: rest, 0, ⟨hK', rfl, hTE, hf'.fp⟩, rfl, hne,
    by simp [hent], hat, hmain', _, hd0, by rw [hfpa]; exact hd1, ⟨ro, s'.mem, rfl, hro, Mem.le_refl _,
      by rw [hfpa]; exact hres⟩, ha.mono hle, hbel.mono hle⟩

end

end LeanVM.Guest.Mode
