module

public import NativeVm.Code.Phase3.Common
public import NativeVm.Code.Phase3.GkrModel
public import NativeVm.Field.Mle

/-!
# The GKR walk's words and the frame of its parts

The GKR walk (`NativeVm.Code.Phase3.Gkr`) keeps the point at `pointR`, from element `rem` (the
remaining depth) on, so that a step's new coordinates `y ++ x` land in place: each sumcheck round
overwrites the coordinate it reads with its challenge, and `y` goes just before. Its other words are
in `tmpR` (`gComb` ... `gY`, numerals through `tmpR_off` and friends): the combiner, the claim, the
remaining depth, the step and `2^step`, the round's point index and count, the round's message, four
ones (for `edot` and `eeqEval`: `dot xs 1 = sumE xs`, `eqEval xs 1 = prodE xs`), the children,
their products, `emle`'s work area, a challenge, `y`.

A part's run is a `Step3` (or, with no transcript step, a `Wrote`) over the small regions it writes;
words apart from them are kept (`Step3.gsame`, the tactics `gsame`, `gsamew`). The tactics of the
block proofs: `gomega` (`omega` on the offsets as numerals), `gmem` (memory through stores),
`gex` (a scratch word exists), `gwrote` (a block's frame), `gok3_tac`, `gap_tac`, `gwithin_tac`.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript

/-! ## The words -/

/-- `tmpR`'s first word. -/
abbrev gT : Nat := tmpR.off
/-- `pointR`'s first word. -/
abbrev gP : Nat := pointR.off
/-- `depthR`'s word. -/
abbrev gD : Nat := depthR.off
/-- `treeR`'s first word. -/
abbrev gTr : Nat := treeR.off
/-- `countR`'s first word. -/
abbrev gCt : Nat := countR.off

theorem tmpR_off : tmpR.off = 54718 := by simp [tmpR, sreg, scratchR_off]
theorem pointR_off : pointR.off = 52704 := by simp [pointR, sreg, scratchR_off]
theorem depthR_off : depthR.off = 52879 := by simp [depthR, sreg, scratchR_off]
theorem treeR_off : treeR.off = 52832 := by simp [treeR, sreg, scratchR_off]
theorem countR_off : countR.off = 52838 := by simp [countR, sreg, scratchR_off]
theorem pointR_size : pointR.size = 128 := rfl
theorem treeR_size : treeR.size = 6 := rfl
theorem countR_size : countR.size = 2 := rfl
theorem depthR_size : depthR.size = 1 := rfl
theorem tmpR_size : tmpR.size = 6144 := rfl

/-- The combiner. -/
abbrev gComb : Nat := gT
/-- The running claim. -/
abbrev gClaim : Nat := gT + 2
/-- The remaining depth. -/
abbrev gRem : Nat := gT + 4
/-- The step's coordinates. -/
abbrev gStep : Nat := gT + 5
/-- `2^step`. -/
abbrev gN : Nat := gT + 6
/-- The sumcheck round's coordinate, as a word index from `gP`. -/
abbrev gPI : Nat := gT + 7
/-- The sumcheck rounds left. -/
abbrev gCnt : Nat := gT + 8
/-- The round's message. -/
abbrev gMsg : Nat := gT + 16
/-- The round's message's tail. -/
abbrev gTail : Nat := gT + 18
/-- Four ones. -/
abbrev gOnes : Nat := gT + 32
/-- Child `j`, at most four elements. -/
abbrev gChild (j : Nat) : Nat := gT + 40 + 8 * j
/-- The three products. -/
abbrev gProd : Nat := gT + 64
/-- `emle`'s work area. -/
abbrev gMle : Nat := gT + 72
/-- A sampled challenge. -/
abbrev gChal : Nat := gT + 80
/-- `y`. -/
abbrev gY : Nat := gT + 84

/-! ## The regions -/

/-- The walk's control words and the round's message. -/
def gA : Region := ⟨tmpR.off, 32⟩
/-- The ones. -/
def gOnesR : Region := ⟨tmpR.off + 32, 8⟩
/-- The children, products, `emle`'s work, a challenge, `y`. -/
def gB : Region := ⟨tmpR.off + 40, 64⟩

def gCombR : Region := ⟨tmpR.off, 2⟩
def gClaimR : Region := ⟨tmpR.off + 2, 2⟩
/-- The words of `step` and `2^step`. -/
def gStepR : Region := ⟨tmpR.off + 5, 2⟩
/-- The words of the rounds' index and count. -/
def gRoundR : Region := ⟨tmpR.off + 7, 2⟩
def gMsgR : Region := ⟨tmpR.off + 16, 2⟩
def gTailR : Region := ⟨tmpR.off + 18, 8⟩
def gChildR (j : Nat) : Region := ⟨tmpR.off + 40 + 8 * j, 8⟩
def gProdR : Region := ⟨tmpR.off + 64, 6⟩
/-- `rem`'s word. -/
def gRemR : Region := ⟨tmpR.off + 4, 1⟩
/-- Tree `j`'s value. -/
def gTrR (j : Nat) : Region := ⟨treeR.off + 2 * j, 2⟩
/-- Product `j`. -/
def gPrdR (j : Nat) : Region := ⟨tmpR.off + 64 + 2 * j, 2⟩
def gMleR : Region := ⟨tmpR.off + 72, 8⟩
def gChalR : Region := ⟨tmpR.off + 80, 2⟩
def gYR : Region := ⟨tmpR.off + 84, 4⟩
/-- The point's elements `i .. i + n`. -/
def gPtR (i n : Nat) : Region := ⟨pointR.off + 2 * i, 2 * n⟩

/-- The regions' offsets as numerals. -/
scoped macro "greg_simp" : tactic => `(tactic| (
  simp only [gA, gOnesR, gB, gCombR, gClaimR, gStepR, gRoundR, gMsgR, gTailR, gChildR, gProdR, gPrdR, gRemR, gTrR, gMleR,
    gChalR, gYR, gPtR, gComb, gClaim, gRem, gStep, gN, gPI, gCnt, gMsg, gTail, gOnes, gChild,
    gProd, gMle, gChal, gY, gT, gP, gD, gTr, gCt, Region.stop, tmpR_off, pointR_off, depthR_off, treeR_off, countR_off,
    pointR_size, treeR_size, countR_size, depthR_size, tmpR_size]))

/-- `omega` after the regions' offsets as numerals. -/
scoped macro "gomega" : tactic => `(tactic| ((try greg_simp) <;> omega))

theorem ok3_scr {r : Region} (h1 : 52670 ≤ r.off) (h2 : r.off + r.size ≤ 85438) : Ok3 r :=
  .inr (.inr ⟨by rw [scratchR_off]; exact h1, by
    simp only [Region.stop, scratchR_off, scratchR_size]; omega⟩)

/-! ## Lists of regions -/

theorem gok3_nil : ∀ r ∈ ([] : List Region), Ok3 r := fun _ h ↦ absurd h List.not_mem_nil

theorem gok3_cons {r : Region} {ws : List Region} (h : Ok3 r) (hs : ∀ q ∈ ws, Ok3 q) :
    ∀ q ∈ r :: ws, Ok3 q := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact h
  · exact hs q hq

/-- Every region of a list is phase 3's. -/
scoped macro "gok3_tac" : tactic => `(tactic| (
  repeat (first | exact gok3_nil | refine gok3_cons (ok3_scr (by gomega) (by gomega)) ?_)))

/-- A region of the scratch is phase 3's. -/
scoped macro "gok3" : tactic => `(tactic| (refine ok3_scr ?_ ?_ <;> gomega))

/-- Words `lo .. lo + n` apart from every region of a list. -/
def GApart (lo n : Nat) (ws : List Region) : Prop := ∀ r ∈ ws, lo + n ≤ r.off ∨ r.stop ≤ lo

theorem gapart_nil (lo n : Nat) : GApart lo n [] := fun _ h ↦ absurd h List.not_mem_nil

theorem gapart_cons {lo n : Nat} {r : Region} {ws : List Region} (h : lo + n ≤ r.off ∨ r.stop ≤ lo)
    (hs : GApart lo n ws) : GApart lo n (r :: ws) := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact h
  · exact hs q hq

/-- Words apart from every region of a list. -/
scoped macro "gap_tac" : tactic => `(tactic| (
  repeat (first | exact gapart_nil _ _ | (refine gapart_cons ?_ ?_; rotate_left))
  all_goals gomega))

/-! ## Frames -/

variable {env : Env} {inp : Input} {t : TState} {s s' : QState}

/-- **Words apart from what a part writes are kept.** -/
theorem Step3.gsame {regs : List Reg64} {ws : List Region} (h : Step3 env regs ws s s')
    (hi : Inputs env inp s.mem) (hws : ∀ r ∈ ws, Ok3 r) {lo n : Nat} (h1 : 69 ≤ lo)
    (h2 : lo + n ≤ 85438) (hap : GApart lo n ws) : Same s.mem s'.mem (wd env.work lo) n := by
  intro k hk
  have := dataEnd_le inp.bytecode.size
  rw [dataEnd_eq] at this
  rw [wd_wd]
  refine h.mem _ (hi.not_foot_work (by rw [workWords_val]; omega) (by omega)) fun r hr ⟨j, hj, e⟩ ↦ ?_
  have hb := (hws r hr).bounds
  rw [layoutR_off, dataEnd_eq] at hb
  unfold Region.stop at hb
  have := (wd_inj (by omega) (by omega)).mp e
  have := hap r hr
  unfold Region.stop at this
  omega

/-- A part's run over smaller regions. -/
theorem Step3.gwithin {regs : List Reg64} {ws ws' : List Region} (h : Step3 env regs ws s s')
    (hw : ∀ r ∈ ws, ∃ q ∈ ws', Within r q) : Step3 env regs ws' s s' := by
  refine ⟨h.rdi, h.regs, fun a hf hr ↦ h.mem a hf fun r hm hin ↦ ?_, h.dom⟩
  obtain ⟨q, hq, hrq⟩ := hw r hm
  exact hr q hq (in_within hin hrq)

theorem Wrote.gwithin {ws ws' : List Region} (h : Wrote env ws s s')
    (hw : ∀ r ∈ ws, ∃ q ∈ ws', Within r q) : Wrote env ws' s s' := by
  refine ⟨h.rdi, fun a hr ↦ h.mem a fun r hm hin ↦ ?_, h.dom⟩
  obtain ⟨q, hq, hrq⟩ := hw r hm
  exact hr q hq (in_within hin hrq)

theorem Step3.gall {regs : List Reg64} {ws : List Region} (h : Step3 env regs ws s s') :
    Step3 env allRegs ws s s' :=
  h.mono (fun r _ ↦ by cases r <;> simp [allRegs]) fun _ h ↦ h

theorem gwithin_cons {r : Region} {ws ws' : List Region} (h : ∃ q ∈ ws', Within r q)
    (hs : ∀ r ∈ ws, ∃ q ∈ ws', Within r q) : ∀ r' ∈ r :: ws, ∃ q ∈ ws', Within r' q := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact h
  · exact hs q hq

theorem gwithin_nil (ws' : List Region) : ∀ r ∈ ([] : List Region), ∃ q ∈ ws', Within r q :=
  fun _ h ↦ absurd h List.not_mem_nil

/-- Each region of a list inside one of another list: name the one by its index. -/
scoped macro "gwithin_tac" : tactic => `(tactic| (
  repeat (first | exact gwithin_nil _ | (refine gwithin_cons ?_ ?_; rotate_left))
  all_goals first
    | (refine ⟨_, List.mem_cons_self, ?_⟩; unfold Within; gomega)
    | (refine ⟨_, (List.mem_cons_of_mem _ List.mem_cons_self), ?_⟩; unfold Within; gomega)
    | (refine ⟨_, (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), ?_⟩; unfold Within; gomega)
    | (refine ⟨_, (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))), ?_⟩; unfold Within; gomega)
    | (refine ⟨_, (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)))), ?_⟩; unfold Within; gomega)
    | (refine ⟨_, (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))), ?_⟩; unfold Within; gomega)))

/-! ## Elements in words -/

theorem EWAt.gof {mem : UInt64 → Option UInt64} {w : UInt64} {k : Nat} {x : EW}
    (h0 : mem (wd w k) = some x.c0) (h1 : mem (wd w (k + 1)) = some x.c1) : EWAt mem (wd w k) x :=
  ⟨h0, by rw [wd_wd]; exact h1⟩

theorem EWAt.gw0 {mem : UInt64 → Option UInt64} {w : UInt64} {k : Nat} {x : EW}
    (h : EWAt mem (wd w k) x) : mem (wd w k) = some x.c0 := h.1

theorem EWAt.gw1 {mem : UInt64 → Option UInt64} {w : UInt64} {k : Nat} {x : EW}
    (h : EWAt mem (wd w k) x) : mem (wd w (k + 1)) = some x.c1 := by
  rw [← wd_wd]; exact h.2

theorem EWArr.gget {mem : UInt64 → Option UInt64} {w : UInt64} {k : Nat} {xs : Array EW}
    (h : EWArr mem (wd w k) xs) {i : Nat} (hi : i < xs.size) : EWAt mem (wd w (k + 2 * i)) xs[i] := by
  rw [← wd_wd]; exact h i hi

theorem EWArr.gof {mem : UInt64 → Option UInt64} {w : UInt64} {k : Nat} {xs : Array EW}
    (h : ∀ i (hi : i < xs.size), EWAt mem (wd w (k + 2 * i)) xs[i]) : EWArr mem (wd w k) xs := by
  intro i hi; rw [wd_wd]; exact h i hi

theorem EWArr.gcons_iff {mem : UInt64 → Option UInt64} {w : UInt64} {k : Nat} {x : EW}
    {xs : Array EW} :
    EWArr mem (wd w k) (#[x] ++ xs) ↔ EWAt mem (wd w k) x ∧ EWArr mem (wd w (k + 2)) xs := by
  constructor
  · intro h
    refine ⟨?_, EWArr.gof fun i hi ↦ ?_⟩
    · have := EWArr.gget h (i := 0) (by simp)
      simpa using this
    · have := EWArr.gget h (i := i + 1) (by simp; omega)
      rw [show k + 2 * (i + 1) = k + 2 + 2 * i by omega] at this
      simpa using this
  · rintro ⟨h0, h⟩
    refine EWArr.gof fun i hi ↦ ?_
    cases i with
    | zero => simpa using h0
    | succ i =>
      have := EWArr.gget h (i := i) (by simp at hi; omega)
      rw [show k + 2 + 2 * i = k + 2 * (i + 1) by omega] at this
      simpa using this

/-- The ones. -/
def gones4 : Array EW := #[1, 1, 1, 1]

theorem gones4_toE (n : Nat) (hn : n ≤ 4) :
    ((gones4.extract 0 n).toList.map EW.toE) = List.replicate n 1 := by
  interval_cases n <;> simp [gones4, NativeVm.Equiv.EW.toE_one]

theorem EWArr.gextract {mem : UInt64 → Option UInt64} {p : UInt64} {xs : Array EW} (h : EWArr mem p xs)
    (n : Nat) : EWArr mem p (xs.extract 0 n) := by
  intro i hi
  simp only [Array.size_extract] at hi
  have := h i (by omega)
  simpa using this

/-! ## Loads and stores in the working area -/

variable {P E : QState → Prop} {xs : List Stmt}

theorem gwp_ldc {d : Reg64} (hrdi : s.reg .rdi = env.ctx) (hw : s.mem (wd env.ctx ctxWork) = some env.work)
    (h : WP (blk xs) (s.setReg d env.work) P E) : WP (blk (I (.load d (cw ctxWork)) :: xs)) s P E :=
  wp_load (eval_cw hrdi ctxWork) hw h

theorem gwp_ldw {b d : Reg64} {k : Nat} {v : UInt64} (hb : s.reg b = env.work)
    (hv : s.mem (wd env.work k) = some v) (h : WP (blk xs) (s.setReg d v) P E) :
    WP (blk (I (.load d (at_ b (wdisp k))) :: xs)) s P E :=
  wp_load (eval_work hb k) hv h

theorem gwp_stw {b r : Reg64} {k : Nat} (hb : s.reg b = env.work)
    (hd : (s.mem (wd env.work k)).isSome)
    (h : WP (blk xs) (s.setMem (wd env.work k) (s.reg r)) P E) :
    WP (blk (I (.store (at_ b (wdisp k)) r) :: xs)) s P E :=
  wp_store (eval_work hb k) hd h

theorem geval_wx {b ix : Reg64} {i k : Nat} (hb : s.reg b = env.work) (hi : s.reg ix = i.toUInt64) :
    ({ base := b, idx := some (ix, .W64), disp := wdisp k } : Addr).eval s = wd env.work (i + k) := by
  rw [eval_idx64 (j := 0) (by rw [hb, wd_zero]) hi, Nat.zero_add]

theorem gwp_ldx {b ix d : Reg64} {i k : Nat} {v : UInt64} (hb : s.reg b = env.work)
    (hi : s.reg ix = i.toUInt64) (hv : s.mem (wd env.work (i + k)) = some v)
    (h : WP (blk xs) (s.setReg d v) P E) :
    WP (blk (I (.load d { base := b, idx := some (ix, .W64), disp := wdisp k }) :: xs)) s P E :=
  wp_load (geval_wx hb hi) hv h

theorem gwp_stx {b ix r : Reg64} {i k : Nat} (hb : s.reg b = env.work) (hi : s.reg ix = i.toUInt64)
    (hd : (s.mem (wd env.work (i + k))).isSome)
    (h : WP (blk xs) (s.setMem (wd env.work (i + k)) (s.reg r)) P E) :
    WP (blk (I (.store { base := b, idx := some (ix, .W64), disp := wdisp k } r) :: xs)) s P E :=
  wp_store (geval_wx hb hi) hd h

/-- A word of a region phase 3 writes exists. -/
theorem gsome {mem : UInt64 → Option UInt64} (hi : Inputs env inp mem) {k : Nat} (h1 : 52670 ≤ k)
    (h2 : k < 85438) : (mem (wd env.work k)).isSome := by
  have := hi.ok3_some (r := scratchR) ok3_scratchR (k := k - 52670)
    (by rw [scratchR_size]; omega)
  rwa [scratchR_off, show 52670 + (k - 52670) = k by omega] at this

/-! ## Block proofs -/

/-- A store at word `a` of a region of the list. -/
theorem Wrote.put {ws : List Region} {s0 : QState} (h : Wrote env ws s0 s) {r : Region} (hr : r ∈ ws)
    {a : Nat} (h1 : r.off ≤ a) (h2 : a < r.off + r.size) (hs : (s0.mem (wd env.work a)).isSome)
    (v : UInt64) : Wrote env ws s0 (s.setMem (wd env.work a) v) := by
  have := h.setMem hr (k := a - r.off) (by omega)
    (by rw [show r.off + (a - r.off) = a by omega, h.dom]; exact hs) v
  rwa [show r.off + (a - r.off) = a by omega] at this

/-- A register write. -/
theorem Wrote.set {ws : List Region} {s0 : QState} (h : Wrote env ws s0 s) {r : Reg64}
    (v : UInt64) (hr : r ≠ .rdi := by decide) : Wrote env ws s0 (s.setReg r v) := h.setReg hr v

/-- A word outside the regions is kept. -/
theorem Wrote.out {ws : List Region} {s0 : QState} (h : Wrote env ws s0 s) (hws : ∀ r ∈ ws, Ok3 r)
    {a : Nat} (ha : a < 85438) (hap : GApart a 1 ws) :
    s.mem (wd env.work a) = s0.mem (wd env.work a) := by
  refine h.mem _ fun r hr ⟨k, hk, e⟩ ↦ ?_
  have := hap r hr
  have hb := (hws r hr).bounds
  rw [dataEnd_eq] at hb
  unfold Region.stop at hb this
  rw [wd_inj (by omega) (by omega)] at e
  omega

/-- The context's word of the working area's address is kept. -/
theorem Wrote.ctxw {ws : List Region} {s0 : QState} (h : Wrote env ws s0 s) (hi : Inputs env inp s0.mem)
    (hws : ∀ r ∈ ws, Ok3 r) : s.mem (wd env.ctx ctxWork) = s0.mem (wd env.ctx ctxWork) := by
  refine h.mem _ fun r hr ⟨k, hk, e⟩ ↦ ?_
  have hb := (hws r hr).bounds
  have := dataEnd_le inp.bytecode.size
  unfold Region.stop at hb
  exact hi.ctx_ne_work (j := ctxWork) (k := r.off + k) (by lay_omega) (by omega) e

/-- A store at word `a` of a region of the list, inside the scratch. -/
theorem Wrote.put' {ws : List Region} {s0 : QState} (hi : Inputs env inp s0.mem) {r : Region} {a : Nat}
    (hb : r.off ≤ a ∧ a < r.off + r.size ∧ 52670 ≤ a ∧ a < 85438) (hr : r ∈ ws)
    (h : Wrote env ws s0 s) (v : UInt64) : Wrote env ws s0 (s.setMem (wd env.work a) v) :=
  h.put hr hb.1 hb.2.1 (gsome hi hb.2.2.1 hb.2.2.2) v

/-- The frame of a block: peel its register writes and stores (each in a region of the list,
its word existing by `hi`), down to a known frame. -/
scoped macro "gwrote" hi:term : tactic => `(tactic| (
  repeat (first
    | with_reducible assumption
    | with_reducible exact Wrote.refl _ _ _
    | with_reducible refine Wrote.set ?_ _
    | (refine Wrote.put' $hi ?_ List.mem_cons_self ?_ _; gomega)
    | (refine Wrote.put' $hi ?_ (List.mem_cons_of_mem _ List.mem_cons_self) ?_ _; gomega)
    | (refine Wrote.put' $hi ?_ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) ?_ _; gomega)
    | (refine Wrote.put' $hi ?_ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) ?_ _; gomega)
    | (refine Wrote.put' $hi ?_ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)))) ?_ _; gomega)
    | (refine Wrote.put' $hi ?_ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))) ?_ _; gomega)
    | fail "gwrote")))

/-- Read memory through register writes and stores to the working area. -/
scoped macro "gmem" : tactic => `(tactic| (
  simp (disch := first | gomega | fail "gmem") only [QState.setReg_mem, QState.setMem_reg, QState.setReg_reg,
    setMem_wd_ne, setMem_wd_eq, reduceCtorEq, ↓reduceIte]))

theorem add_wdisp (b : UInt64) (k : Nat) : b + (wdisp k).toUInt64 = wd b k := by
  rw [wdisp_toUInt64]; rfl

/-- A kernel's run: memory kept, `rdi` kept. -/
theorem Wrote.kern {ws : List Region} {s0 s1 : QState} {regs : List Reg64} (h : Wrote env ws s0 s)
    (hm : s1.mem = s.mem) (hf : RegsFrame regs s s1) (hr : Reg64.rdi ∉ regs := by decide) :
    Wrote env ws s0 s1 :=
  ⟨(hf .rdi hr).trans h.rdi, fun a ha ↦ by rw [hm]; exact h.mem a ha, fun a ↦ by rw [hm]; exact h.dom a⟩

theorem gsm {a a' v : UInt64} (h : (s.mem a').isSome) : ((s.setMem a v).mem a').isSome := by
  rw [QState.setMem_mem]; split <;> simp_all

theorem gsr {a' v : UInt64} {r : Reg64} (h : (s.mem a').isSome) : ((s.setReg r v).mem a').isSome := h

theorem gwd {ws : List Region} {s0 : QState} {a : UInt64} (hw : Wrote env ws s0 s)
    (h : (s0.mem a).isSome) : (s.mem a).isSome := by rw [hw.dom]; exact h

/-- A word of the scratch exists, through stores, register writes and known frames. -/
scoped macro "gex" hi:term : tactic => `(tactic| (
  repeat (first
    | with_reducible refine gsm ?_
    | with_reducible refine gsr ?_
    | (apply gwd; with_reducible assumption))
  exact gsome $hi (by gomega) (by gomega)))

theorem NatAt.gkeep {mem mem' : UInt64 → Option UInt64} {p : UInt64} {n : Nat} (hx : NatAt mem p n)
    (h : Same mem mem' p 1) : NatAt mem' p n := ⟨hx.1, h.base (by omega) hx.2⟩

/-- A `Same` goal from a part's run (`Step3`) apart from what it writes. -/
scoped macro "gsame" hst:term "," hi:term : tactic => `(tactic| (
  refine Step3.gsame $hst $hi ?_ ?_ ?_ ?_; gok3_tac; gomega; gomega; gap_tac))

/-- A `Same` goal from a run of code with no transcript step (`Wrote`). -/
scoped macro "gsamew" hw:term "," hi:term : tactic => `(tactic| (
  refine Step3.gsame (Wrote.step $hw) $hi ?_ ?_ ?_ ?_; gok3_tac; gomega; gomega; gap_tac))

/-- Two runs as one, over all the registers and the regions of both. -/
theorem Step3.gtrans {r1 r2 : List Reg64} {w1 w2 ws : List Region} {s1 s2 : QState}
    (h1 : Step3 env r1 w1 s s1) (h2 : Step3 env r2 w2 s1 s2) (hw1 : ∀ r ∈ w1, r ∈ ws)
    (hw2 : ∀ r ∈ w2, r ∈ ws) : Step3 env allRegs ws s s2 :=
  (h1.gall.mono (fun _ h ↦ h) hw1).trans (h2.gall.mono (fun _ h ↦ h) hw2)

end NativeVm.Code.P3
