module

public import NativeVm.Code.Phase7.Frame
public import NativeVm.Field.Arrays

/-!
# Phase 7: reading and sampling a counted run of elements into the area

`readScalarsC cnt dst` / `sampleChallengesC cnt dst`: the count `n` from work word `cnt`, then
`readScalars n` / `sampleChallenges n`, element `i` stored at work words `dst + 2 i`, `dst + 2 i + 1`.
One loop (`loopC`) for both: the count left in `r12`, the next element's address in `r13` (the
gadgets keep both); the count is read before any store, so it may lie in the destination.
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model
open NativeVm.Transcript (wd Env ctxWork clobbers wd_inj wd_add wp_load wp_store wp_reg cond_ne
  rhs_imm eval_cw)
open NativeVm.Field (eval_at int64Zero_toUInt64 toUInt64_eq_zero toUInt64_succ_sub)

/-- Run the gadget `g` `n` times, `n` at work word `cnt`, storing its results (`r9`, `r10`) at work
words `dst + 2 i`, `dst + 2 i + 1`. -/
def loopC (g : Stmt) (cnt dst : Nat) : Stmt := blk [ldW, ldw .r12 cnt, leaw .r13 dst,
  .loop (.cmp .ne .r12 (.imm 0)) (blk [g,
    I (.store (at_ .r13 0) .r9), I (.store (at_ .r13 8) .r10),
    I (.addi .r13 16), I (.subi .r12 1)])]

/-- `readScalars n`, `n` at work word `cnt`, into work words from `dst`. -/
def readScalarsC (cnt dst : Nat) : Stmt := loopC Transcript.readScalar cnt dst

/-- `sampleChallenges n`, `n` at work word `cnt`, into work words from `dst`. -/
def sampleChallengesC (cnt dst : Nat) : Stmt := loopC Transcript.sampleChallenge cnt dst

variable {p : Par}

/-- The loop's state after `j` passes. -/
def LoopInv (p : Par) (m0 : UInt64 → Option UInt64) (n dst j : Nat) (acc : Array EW)
    (s : QState) : Prop :=
  acc.size = j ∧ EWArr s.mem (wd p.env.work dst) acc ∧
    Only p.env (fun k ↦ dst ≤ k ∧ k < dst + 2 * n) m0 s.mem ∧
    s.reg .r12 = (n - j).toUInt64 ∧ s.reg .r13 = wd p.env.work (dst + 2 * j)

/-- The gadgets keep the loop's state. -/
theorem loopInv_gok {m0 : UInt64 → Option UInt64} {n dst j : Nat} {acc : Array EW}
    (hdst : mineLo ≤ dst ∧ dst + 2 * n ≤ dataEnd) (hj : j ≤ n) :
    GOk p.env p.inp (LoopInv p m0 n dst j acc) := by
  rintro s s' ⟨hsz, harr, hon, h12, h13⟩ hi hk -
  have hm : ∀ k, mineLo ≤ k → k < dataEnd →
      s'.mem (wd p.env.work k) = s.mem (wd p.env.work k) :=
    fun k h1 h2 ↦ keeps_mine hi hk (inMine_wd h1 h2)
  refine ⟨hsz, fun i hi' ↦ ?_, fun k h1 h2 hk' ↦ (hm k h1 h2).trans (hon k h1 h2 hk'),
    (hk.regs .r12 (by simp [clobbers])).trans h12, (hk.regs .r13 (by simp [clobbers])).trans h13⟩
  have := harr i hi'
  simp only [EWAt, wd_wd] at this ⊢
  rw [hm _ (by omega) (by omega), hm _ (by omega) (by omega)]
  exact this

/-- Two stores push an element. -/
theorem ewarr_push2 {mem : UInt64 → Option UInt64} {b : UInt64} {dst : Nat} {acc : Array EW}
    {x : EW} (h : EWArr mem (wd b dst) acc) (hb : dst + 2 * acc.size + 1 < 2 ^ 61) :
    EWArr (Function.update (Function.update mem (wd b (dst + 2 * acc.size)) (some x.c0))
      (wd b (dst + 2 * acc.size + 1)) (some x.c1)) (wd b dst) (acc.push x) := by
  intro i hi
  rw [Array.size_push] at hi
  rw [Array.getElem_push]
  simp only [EWAt, wd_wd]
  have ne : ∀ a c, a ≠ c → a < 2 ^ 61 → c < 2 ^ 61 → wd b a ≠ wd b c := fun a c hac ha hc e ↦
    hac ((wd_inj ha hc).mp e)
  split
  · have := h i ‹_›
    simp only [EWAt, wd_wd] at this
    rw [Function.update_of_ne (ne _ _ (by omega) (by omega) hb),
      Function.update_of_ne (ne _ _ (by omega) (by omega) (by omega)),
      Function.update_of_ne (ne _ _ (by omega) (by omega) hb),
      Function.update_of_ne (ne _ _ (by omega) (by omega) (by omega))]
    exact this
  · rw [show i = acc.size by omega, Function.update_of_ne (ne _ _ (by omega) (by omega) hb),
      Function.update_self, Function.update_self]
    exact ⟨rfl, rfl⟩

/-- **The loop of a gadget into the area.** -/
theorem loopC_spec {g : Stmt} {mg : VM EW}
    (hg : ∀ {R : QState → Prop}, GOk p.env p.inp R → Refines (fun t s ↦ Base p t s ∧ R s) g mg
      (fun x t s ↦ Base p t s ∧ R s ∧ s.reg .r9 = x.c0 ∧ s.reg .r10 = x.c1) (Err p))
    {m0 : UInt64 → Option UInt64} {n cnt dst : Nat}
    (hdst : mineLo ≤ dst ∧ dst + 2 * n ≤ dataEnd) :
    Refines (fun t s ↦ Base p t s ∧ s.mem = m0 ∧ NatAt s.mem (wd p.env.work cnt) n)
      (loopC g cnt dst) ((List.range n).foldlM (fun acc _ ↦ do pure (acc.push (← mg))) #[])
      (fun xs t s ↦ Base p t s ∧ EWArr s.mem (wd p.env.work dst) xs ∧ xs.size = n ∧
        Only p.env (fun k ↦ dst ≤ k ∧ k < dst + 2 * n) m0 s.mem) (Err p) := by
  have hde := dataEnd_eq
  have key := Refines.foldlM (l := List.range n)
    (f := fun (acc : Array EW) (_ : Nat) ↦ do pure (acc.push (← mg)))
    (cond := .cmp .ne .r12 (.imm 0)) (body := blk [g,
      I (.store (at_ .r13 0) .r9), I (.store (at_ .r13 8) .r10),
      I (.addi .r13 16), I (.subi .r12 1)]) (E := Err p)
    (Inv := fun j acc t s ↦ Base p t s ∧ LoopInv p m0 n dst j acc s) ?_ ?_ (init := #[])
  · rintro t s ⟨hb, hm, hc⟩
    unfold loopC ldW ldw leaw
    refine wp_load (eval_cw hb.rdi ctxWork) hb.workPtr ?_
    have hW : (s.setReg .rbp p.env.work).reg .rbp = p.env.work := by rsimp
    refine wp_load (eval_w hW cnt) (by rsimp; exact hc.2) ?_
    refine wp_reg (by simp only [QInstr.step]; rfl) ?_
    show WP (Stmt.loop _ _) _ _ _
    refine WP.mono (key t _ ?_) ?_ fun _ h ↦ h
    · refine ⟨hb.frM ⟨by rsimp, fun _ ↦ rfl, fun _ _ ↦ rfl⟩, rfl, fun i hi ↦ absurd hi (by simp),
        ?_, by rsimp; simp, ?_⟩
      · rw [QState.setReg_mem, QState.setReg_mem, QState.setReg_mem, hm]
        exact Only.refl _ _
      · rsimp
        exact eval_w (by rsimp) dst
    · rintro s' ⟨xs, t', hrun, hb', hsz, harr, hon, -, -⟩
      rw [List.length_range] at hsz
      exact ⟨xs, t', hrun, hb', harr, hsz, hon⟩
  · rintro j acc t s ⟨-, -, -, -, h12, -⟩
    rw [List.length_range, cond_ne, rhs_imm, h12, int64Zero_toUInt64, bne_iff_ne, ne_eq]
    constructor
    · intro hne
      by_contra hjn
      exact hne (by rw [show n - j = 0 by omega]; rfl)
    · intro hjn e
      have := toUInt64_eq_zero (show n - j < 2 ^ 64 by omega) e
      omega
  · intro j hj acc
    rw [List.length_range] at hj
    show Refines _ _ (mg >>= fun x ↦ pure (acc.push x)) _ _
    refine Refines.blk_cons (hg (loopInv_gok hdst hj.le)) fun x ↦ Refines.pure ?_
    rintro t s ⟨hb, ⟨hsz, harr, hon, h12, h13⟩, h9, h10⟩
    have hww := workWords_ge p.inp.bytecode.size
    have hsome : ∀ k, k < dataEnd → (s.mem (wd p.env.work k)).isSome :=
      fun k hk ↦ hb.inp.workSome k (by omega)
    have h0 := hsome (dst + 2 * j) (by omega)
    have h1 := hsome (dst + 2 * j + 1) (by omega)
    refine wp_store (by rw [eval_at, h13, int64Zero_toUInt64, UInt64.add_zero]) h0 ?_
    have e1 : (at_ .r13 8).eval (s.setMem (wd p.env.work (dst + 2 * j)) (s.reg .r9)) =
        wd p.env.work (dst + 2 * j + 1) := by
      rw [eval_at, QState.setMem_reg, h13,
        show (8 : Int64).toUInt64 = (8 * 1 : Nat).toUInt64 from rfl, wd_add]
    refine wp_store e1 (by rw [NativeVm.Transcript.isSome_setMem _ _ h0]; exact h1) ?_
    refine wp_reg rfl (wp_reg rfl (WP.blk_nil ?_))
    have hmem : ((s.setMem (wd p.env.work (dst + 2 * j)) (s.reg .r9)).setMem
        (wd p.env.work (dst + 2 * j + 1))
        ((s.setMem (wd p.env.work (dst + 2 * j)) (s.reg .r9)).reg .r10)).mem =
        Function.update (Function.update s.mem (wd p.env.work (dst + 2 * j)) (some x.c0))
          (wd p.env.work (dst + 2 * j + 1)) (some x.c1) := by
      rw [QState.setMem_reg, h9, h10]
      rfl
    refine ⟨hb.frM ⟨by rsimp, fun a ↦ ?_, fun a ha ↦ ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [QState.setReg_mem, QState.setReg_mem, NativeVm.Transcript.isSome_setMem _ _
        (by rw [NativeVm.Transcript.isSome_setMem _ _ h0]; exact h1),
        NativeVm.Transcript.isSome_setMem _ _ h0]
    · rw [QState.setReg_mem, QState.setReg_mem, hmem,
        Function.update_of_ne (fun e ↦ ha (by subst e; exact inMine_wd (by omega) (by omega))),
        Function.update_of_ne (fun e ↦ ha (by subst e; exact inMine_wd (by omega) (by omega)))]
    · rw [Array.size_push, hsz]
    · rw [QState.setReg_mem, QState.setReg_mem, hmem, ← hsz]
      exact ewarr_push2 harr (by omega)
    · rw [QState.setReg_mem, QState.setReg_mem, hmem]
      exact (hon.store ⟨by omega, by omega⟩ (by omega) _).store ⟨by omega, by omega⟩ (by omega) _
    · rsimp
      rw [h12, show n - j = (n - (j + 1)) + 1 by omega, toUInt64_succ_sub]
    · rsimp
      rw [h13, show (16 : UInt64) = (8 * 2 : Nat).toUInt64 from rfl, wd_add]
      congr 1

theorem readScalarsC_spec {p : Par} {m0 : UInt64 → Option UInt64} {n cnt dst : Nat}
    (_hcnt : mineLo ≤ cnt ∧ cnt < dataEnd) (hdst : mineLo ≤ dst ∧ dst + 2 * n ≤ dataEnd)
    (_hn : n ≤ 64) :
    Refines (fun t s ↦ Base p t s ∧ s.mem = m0 ∧ NatAt s.mem (wd p.env.work cnt) n)
      (readScalarsC cnt dst) (readScalars n)
      (fun xs t s ↦ Base p t s ∧ EWArr s.mem (wd p.env.work dst) xs ∧ xs.size = n ∧
        Only p.env (fun k ↦ dst ≤ k ∧ k < dst + 2 * n) m0 s.mem) (Err p) :=
  loopC_spec readScalar_b hdst

theorem sampleChallengesC_spec {p : Par} {m0 : UInt64 → Option UInt64} {n cnt dst : Nat}
    (_hcnt : mineLo ≤ cnt ∧ cnt < dataEnd) (hdst : mineLo ≤ dst ∧ dst + 2 * n ≤ dataEnd)
    (_hn : n ≤ 64) :
    Refines (fun t s ↦ Base p t s ∧ s.mem = m0 ∧ NatAt s.mem (wd p.env.work cnt) n)
      (sampleChallengesC cnt dst) (sampleChallenges n)
      (fun xs t s ↦ Base p t s ∧ EWArr s.mem (wd p.env.work dst) xs ∧ xs.size = n ∧
        Only p.env (fun k ↦ dst ≤ k ∧ k < dst + 2 * n) m0 s.mem) (Err p) :=
  loopC_spec sample_b hdst

end NativeVm.Code.P7
