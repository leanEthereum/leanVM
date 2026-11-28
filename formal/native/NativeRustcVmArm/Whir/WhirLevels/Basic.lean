module

public import NativeRustcVmArm.Whir.WhirLevels.Exec
public import NativeRustcVmArm.Whir.WhirLevels.Model
public import NativeRustcVmArm.Whir.WhirLevels.Basis
public import NativeRustcVmArm.Whir.TFrame
public import NativeRustcVmArm.Whir.FoldRounds.Basic

/-!
# `whir_levels`: its frame, its context, its invariants

From the entry `m0` (the `TState` X0, `logN` X1, `laneFolds` X2, the basis X3, the levels X4, their
count X5, the state X6): the 96-byte frame (`WFr`, X30 and X19 to X28 saved, X29 kept), the
outputs (`outs`: the `WhirW` and the `TState`), the entry's facts (`Ctx`, the levels the ladder
`ladderW logN rate`), the registers the prologue sets (`Regs`). `Head k`: before level `k`'s fold
rounds, the run so far the model's; `Mid k`: after them.
-/

namespace NativeRustcVmArm.Whir.WhirLevels

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Layout.Ladder

@[expose] public section

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(0, .X30), (16, .X28), (24, .X27), (32, .X26), (40, .X25), (48, .X24), (56, .X23),
    (64, .X22), (72, .X21), (80, .X20), (88, .X19)]

/-- The callee-saved register the function never writes. -/
def keep : List XReg := [.X29]

/-- The `TState`. -/
abbrev tA (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
/-- The `WhirW`. -/
abbrev pA (m0 : MachineData) : BitVec 64 := m0.regs.X6.toBitVec
/-- The levels. -/
abbrev lvA (m0 : MachineData) : BitVec 64 := m0.regs.X4.toBitVec
/-- The basis. -/
abbrev bA (m0 : MachineData) : BitVec 64 := m0.regs.X3.toBitVec
/-- `logN`. -/
abbrev logN (m0 : MachineData) : Nat := m0.regs.X1.toNat
/-- `laneFolds`. -/
abbrev lf (m0 : MachineData) : Nat := m0.regs.X2.toNat

/-- The outputs. -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange (pA m0) whirBytes q ∨ InRange (tA m0) tstateBytes q

/-- The frame. -/
abbrev WFr (m0 st : MachineData) : Prop := Fr m0 96 whirLevelsStack slots keep (outs m0) st

/-- Level `k` of the ladder `ladderW μ r`. -/
abbrev lvl (μ r k : Nat) : Whir.Level := ⟨foldAt k, r + 3 * k, qAt μ r k⟩

/-- The whole run. -/
abbrev runAll (s0 : TState) (levels : List Whir.Level) (b : BasisW) (claim : EW)
    (m0 : MachineData) : Option (Unit × TState) :=
  (whirLevels (logN m0) (lf m0) b 0 levels ⟨claim, #[], #[]⟩).run s0

/-- The registers the prologue sets: the state, the basis, the `TState`, `laneFolds`, the levels,
the last level's index, `logN`, the second level, the rounds' offset (the level count in X26 is
`Head`'s and `Mid`'s). -/
structure Regs (m0 : MachineData) (len : Nat) (st : MachineData) : Prop where
  x19 : st.regs.getXReg .X19 = m0.regs.X6
  x20 : st.regs.getXReg .X20 = m0.regs.X3
  x21 : st.regs.getXReg .X21 = m0.regs.X0
  x22 : st.regs.getXReg .X22 = m0.regs.X2
  x23 : st.regs.getXReg .X23 = m0.regs.X4
  x24 : (st.regs.getXReg .X24).toNat = len - 1
  x25 : st.regs.getXReg .X25 = m0.regs.X1
  x27 : (st.regs.getXReg .X27).toBitVec = m0.regs.X4.toBitVec + 24#64
  x28 : (st.regs.getXReg .X28).toNat = 61152

/-- X26 at level `k`: the level count, or for the sixth level its address. -/
def X26Ok (m0 : MachineData) (len k : Nat) (st : MachineData) : Prop :=
  if k < 5 then (st.regs.getXReg .X26).toNat = len
  else (st.regs.getXReg .X26).toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 120

section
variable [Labels]

/-- **The entry's facts**, the levels the ladder of `logN` at the rate exponent `rate`. -/
structure Ctx (a : DecArea) (s0 : TState) (levels : List Whir.Level) (ba : BasisAddrs)
    (b : BasisW) (claim : EW) (m0 : MachineData) (rate : Nat) : Prop where
  stack : StackOk m0 whirLevelsStack
  rc : RcAt m0 whirLevelsStack
  ro : RodataAt m0 whirLevelsStack
  tok : TStateOk m0 (tA m0) a whirLevelsStack
  tro : NativeRustcVm.RodataApart rodataAddr (tA m0) tstateBytes
  ts0 : TStateAt m0.dmem (tA m0) a s0
  roots0 : s0.roots.size + levels.length ≤ maxRoots
  adm : Whir.Admissible (logN m0) rate
  lad : levels = ladderW (logN m0) rate
  len : levels.length = m0.regs.X5.toNat
  lvs : LevelsAt m0.dmem (lvA m0) levels
  bw : BasisWAt m0.dmem (bA m0) ba b
  ws0 : WhirStateAt m0.dmem (pA m0) ⟨claim, #[], #[]⟩
  pout : WhirOut m0 (tA m0) a (pA m0) whirBytes whirLevelsStack
  lin : WhirIn m0 (lvA m0) (levelBytes * levels.length) whirLevelsStack
  lp : Apart (lvA m0) (levelBytes * levels.length) (pA m0) whirBytes
  lt : Apart (lvA m0) (levelBytes * levels.length) (tA m0) tstateBytes
  bp : BasisIn m0 (bA m0) ba whirLevelsStack (pA m0) whirBytes
  bt : BasisIn m0 (bA m0) ba whirLevelsStack (tA m0) tstateBytes
  bap : BasisApart (bA m0) ba

/-- **Before level `k`'s fold rounds**: the frame, the registers, the `TState` `s` and the state
`w` (`alphasAt k` `α`s, `2 k` glued claims), room for a root per level left, the run the model's
from level `k`. -/
structure Head (a : DecArea) (s0 : TState) (levels : List Whir.Level) (b : BasisW) (claim : EW)
    (m0 : MachineData) (k : Nat) (s : TState) (w : WhirStateW) (st : MachineData) : Prop where
  fr : WFr m0 st
  regs : Regs m0 levels.length st
  ts : TStateAt st.dmem (tA m0) a s
  ws : WhirStateAt st.dmem (pA m0) w
  lt : k < levels.length
  alphas : w.alphas.size = alphasAt k
  glued : w.glued.size = 2 * k
  roots : s.roots.size + (levels.length - k) ≤ maxRoots
  run : runAll s0 levels b claim m0 =
    (whirLevels (logN m0) (lf m0) b k (levels.drop k) w).run s

/-- **After level `k`'s fold rounds**: the `TState` `s`, the state `w` and the rounds `rs`, the run
the model's `final_level` or `next_level` then the levels after; X26 the level count, or after
the sixth level's fold rounds the sixth level's address. -/
structure Mid (a : DecArea) (s0 : TState) (levels : List Whir.Level) (b : BasisW) (claim : EW)
    (m0 : MachineData) (rate k : Nat) (s : TState) (w : WhirStateW) (rs : Array FoldRoundW)
    (st : MachineData) : Prop where
  fr : WFr m0 st
  regs : Regs m0 levels.length st
  x26 : X26Ok m0 levels.length k st
  ts : TStateAt st.dmem (tA m0) a s
  wa : WhirAt st.dmem (pA m0) w rs
  lt : k < levels.length
  alphas : w.alphas.size = alphasAt (k + 1)
  glued : w.glued.size = 2 * k
  roots : s.roots.size + (levels.length - k) ≤ maxRoots
  fin : k + 1 = levels.length → runAll s0 levels b claim m0 =
    (finalLevelM k (lvl (logN m0) rate k) (logN m0 - w.alphas.size) (lf m0) b w rs).run s
  nxt : k + 1 < levels.length → runAll s0 levels b claim m0 =
    ((nextLevelM k (lvl (logN m0) rate k) (lvl (logN m0) rate (k + 1)) (logN m0 - w.alphas.size)
      w rs).run s).bind fun p ↦
        (whirLevels (logN m0) (lf m0) b (k + 1) (levels.drop (k + 1)) p.1).run p.2

/-- The function's goal. -/
abbrev Goal (a : DecArea) (s0 : TState) (levels : List Whir.Level) (b : BasisW) (claim : EW)
    (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ WhirLevelsPost a s0 levels b claim m0 st.data

end

end

public section

theorem stack_val : whirLevelsStack = 11520 ∧ foldRoundsStack = 960 ∧ nextLevelStack = 11424 ∧
    finalLevelStack = 5856 := by
  decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 96 := by decide

theorem keep_saved : ∀ r ∈ keep, calleeSaved r = true := by decide

/-- The frame's bytes are in the entry's stack. -/
theorem frame_sub {m0 : MachineData} {F N : Nat} (hN : N ≤ m0.regs.SP.toNat) (hF : F ≤ N)
    {q : BitVec 64} (hq : InRange (base m0 F) F q) : InRange (stackBelow m0 N) N q := by
  have e1 := base_toNat (m0 := m0) (F := F) (by omega)
  have e2 := base_toNat (m0 := m0) (F := N) hN
  exact NativeRustcVm.InRange.mono hq (base_noWrap (by omega)) (base_noWrap hN)
    (by show (base m0 N).toNat ≤ _; omega) (by show _ ≤ (base m0 N).toNat + _; omega)

section
variable [Labels] {a : DecArea} {s0 : TState} {levels : List Whir.Level} {ba : BasisAddrs}
  {b : BasisW} {claim : EW} {m0 : MachineData} {rate : Nat}

theorem Ctx.of_pre (h : WhirLevelsPre a s0 levels ba b claim m0) :
    ∃ rate, Ctx a s0 levels ba b claim m0 rate := by
  obtain ⟨⟨hS, hrc, hro, htok, htro⟩, hts, hroots, ⟨rate, hlad⟩, hlen, hlvs, hbw, hws, hpo, hlin,
    hlp, hlt, hbp, hbt, hbap⟩ := h
  by_cases hadm : Whir.Admissible (logN m0) rate
  · rw [ladder_eq hadm, Option.some.injEq] at hlad
    exact ⟨rate, hS, hrc, hro, htok, htro, hts, hroots, hadm, hlad.symm, hlen, hlvs, hbw, hws, hpo,
      hlin, hlp, hlt, hbp, hbt, hbap⟩
  · rw [ladder_none hadm] at hlad
    cases hlad

namespace Ctx

variable (c : Ctx a s0 levels ba b claim m0 rate)
include c

theorem hN : whirLevelsStack ≤ m0.regs.SP.toNat := c.stack.2.1

theorem logN_le : 16 ≤ logN m0 ∧ logN m0 ≤ 30 := by
  have := admissible_iff.mp c.adm; omega

theorem len_eq : levels.length = nOf (logN m0) := by rw [c.lad, length_ladderW]

theorem len_le : 3 ≤ levels.length ∧ levels.length ≤ 6 := by
  rw [c.len_eq]; exact nOf_le _

theorem getElem {k : Nat} (h : k < levels.length) : levels[k] = lvl (logN m0) rate k := by
  have h' : k < (ladderW (logN m0) rate).length := by rw [← c.lad]; exact h
  simp only [c.lad]
  exact ladderW_getElem h'

theorem drop_eq {k : Nat} (h : k < levels.length) :
    levels.drop k = lvl (logN m0) rate k :: levels.drop (k + 1) := by
  rw [drop_cons h, c.getElem h]

theorem outs_not_frame {F : Nat} (hF : F ≤ whirLevelsStack) {q : BitVec 64} (hq : outs m0 q) :
    ¬InRange (base m0 F) F q := fun hf ↦ by
  have hs := frame_sub c.hN hF hf
  have hnN := base_noWrap (m0 := m0) (F := whirLevelsStack) c.hN
  have hfp := c.ts0.footprint
  rcases hq with hq | hq
  · exact NativeRustcVm.Apart.not_inRange c.pout.1.2.2.2.2.1 c.pout.1.2.1 hnN hq hs
  · exact NativeRustcVm.Apart.not_inRange c.tok.1 hfp.1.2 hnN hq hs

/-- **The context of the calls**, from a frame of `F` bytes. -/
theorem tctx {F : Nat} (hF : F ≤ whirLevelsStack) (h16 : F % 16 = 0) :
    TCtx m0 F whirLevelsStack (tA m0) a (outs m0) := by
  have hfp := c.ts0.footprint
  have hrc := c.rc
  have hpo := c.pout.1
  have hnt : NoWrap (tA m0) tstateBytes := hfp.1.2
  have hnd : NoWrap a.words (8 * a.len) := hfp.2.1.2
  refine ⟨c.stack, hrc, c.tok, hfp, hF, h16, fun q hq hr ↦ ?_, fun q hq hd ↦ ?_,
    fun q hq ↦ Or.inr hq, fun q hq ↦ c.outs_not_frame hF hq⟩
  · rcases hq with hq | hq
    · exact NativeRustcVm.Apart.not_inRange hpo.2.2.2.2.2 hpo.2.1 hrc.2.1 hq hr
    · exact NativeRustcVm.Apart.not_inRange c.tok.2.2 hnt hrc.2.1 hq hr
  · rcases hq with hq | hq
    · exact NativeRustcVm.Apart.not_inRange hpo.2.2.2.1 hpo.2.1 hnd hq hd
    · exact NativeRustcVm.Apart.not_inRange hfp.2.2 hnt hnd hq hd

/-- Bytes apart from the stack and the outputs stay the same in the frame's states. -/
theorem same {st : MachineData} (hf : WFr m0 st) {x : BitVec 64} {n : Nat} (hnw : NoWrap x n)
    (hs : Apart x n (stackBelow m0 whirLevelsStack) whirLevelsStack)
    (hp : Apart x n (pA m0) whirBytes) (ht : Apart x n (tA m0) tstateBytes) :
    NativeRustcVm.Layout.Same m0.dmem st.dmem x n := by
  have hfp := c.ts0.footprint
  refine NativeRustcVm.Layout.Same.of_sameOutside hf.same fun j hj hq ↦ ?_
  rcases hq with hq | hq | hq
  · exact NativeRustcVm.Apart.not_inRange_add hs hnw (base_noWrap c.hN) hj hq
  · exact NativeRustcVm.Apart.not_inRange_add hp hnw c.pout.1.2.1 hj hq
  · exact NativeRustcVm.Apart.not_inRange_add ht hnw hfp.1.2 hj hq

/-- The levels in the frame's states. -/
theorem levels_at {st : MachineData} (hf : WFr m0 st) : LevelsAt st.dmem (lvA m0) levels := by
  have hs := c.same hf c.lin.1.2 c.lin.2 c.lp c.lt
  intro i hi
  obtain ⟨h1, h2, h3, h4⟩ := c.lvs i hi
  refine ⟨h1, h2, h3, NativeRustcVm.Tables.WordsAt.of_same h4
    (hs.sub (o := levelBytes * i) (k := 24) ?_) (by simp)⟩
  have : levelBytes * (i + 1) ≤ levelBytes * levels.length := Nat.mul_le_mul_left _ hi
  unfold levelBytes at this ⊢
  omega

/-- The basis in the frame's states. -/
theorem basis_at {st : MachineData} (hf : WFr m0 st) : BasisWAt st.dmem (bA m0) ba b :=
  basisWAt_of_same c.bw (c.same hf c.bp.1.1.2 c.bp.1.2 c.bp.2.1 c.bt.2.1) fun r hr ↦
    c.same hf (c.bp.2.2 r hr).1.1.2 (c.bp.2.2 r hr).1.2 (c.bp.2.2 r hr).2 (c.bt.2.2 r hr).2

end Ctx

end

end

end NativeRustcVmArm.Whir.WhirLevels
