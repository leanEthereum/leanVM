import Rv64Verifier.Proofs.Pcs.VsoLevel
import Rv64Verifier.Proofs.Pcs.VsoFoldModel

/-!
# `verify_stacked_opening`'s level loop: the fold rounds

At a level's head (`0x8000a190`) the fold count `fc` and the rate are read off the ladders, and
`level_folds` (`Vec<E>`, at `S - 640`) starts empty; each round (`0x8000a1e8`) draws a
challenge (`duplex`, its lanes to `S - 128`), pushes it to `folds` and to `level_folds` (each
through `grow_one` when full), evaluates the running quadratic at it (`poly_eval` into
`S - 464`) and reads the next one (`sumcheck_round_poly` into `S - 160`), whose `Err` is
returned (`0x8000b84c`). Registers through the rounds: `s8` the folds' length at the level's
head, `s2` 24 times it, `s3` `level_folds`' buffer, `s4`/`s5` 24 times / the rounds done, `s6`/`s7`
the running quadratic.

What the rounds write from the head on is `FW`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## The level's ladder entries -/

/-- Level `ℓ`'s fold count. -/
def fcOf (s : MachineState) (ℓ : ℕ) : ℕ := (Model.Pcs.ladderFolds (K0 s + 1)).getD ℓ 0

/-- Level `ℓ`'s rate. -/
def rtOf (s : MachineState) (ℓ : ℕ) : ℕ :=
  (Model.Pcs.ladderRates (s.getReg .x13).toNat (K0 s + 1)).getD ℓ 0

theorem fcOf_eq (s : MachineState) {ℓ : ℕ} (h : ℓ < K0 s + 2) :
    fcOf s ℓ = if ℓ = 0 then 6 else 4 := by
  cases ℓ with
  | zero => rfl
  | succ i =>
    simp only [fcOf, Model.Pcs.ladderFolds, List.getD_cons_succ, Nat.add_one_ne_zero, ite_false]
    rw [List.getD_eq_getElem _ _ (by simp; omega)]
    simp

theorem lw_getD (l : List ℕ) (i : ℕ) : (lw l).getD i 0 = BitVec.ofNat 64 (l.getD i 0) := by
  simp only [lw, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

theorem zip_drop (s : MachineState) {ℓ : ℕ} (hℓ : ℓ < K0 s + 2) :
    ((cfgOf s).folds.zip (cfgOf s).logInvRates).drop ℓ =
      (fcOf s ℓ, rtOf s ℓ) :: ((cfgOf s).folds.zip (cfgOf s).logInvRates).drop (ℓ + 1) := by
  have h1 : ℓ < (cfgOf s).folds.length := by
    simp only [cfgOf, Model.Pcs.ladderFolds, List.length_cons, List.length_replicate]; omega
  have h2 : ℓ < (cfgOf s).logInvRates.length := by
    simp only [cfgOf, Model.Pcs.ladderRates, List.length_cons, List.length_map, List.length_range]
    omega
  have hlen : ℓ < ((cfgOf s).folds.zip (cfgOf s).logInvRates).length := by
    rw [List.length_zip]; omega
  rw [List.drop_eq_getElem_cons hlen, List.getElem_zip]
  congr 2
  · exact (List.getD_eq_getElem _ _ h1).symm
  · exact (List.getD_eq_getElem _ _ h2).symm

/-- What the level runs after its fold rounds. -/
abbrev AFk (s : MachineState) (x : LCtx) (ℓ : ℕ) :
    Model.Pcs.WhirLocals × List E → Model.TM Unit :=
  Model.Pcs.afterFolds (s.getReg .x12).toNat (cfgOf s) (basisOf s x) ℓ (fcOf s ℓ) (rtOf s ℓ)
    (((cfgOf s).folds.zip (cfgOf s).logInvRates).drop (ℓ + 1))

theorem foldSt_nil (Wl : Model.Pcs.WhirLocals) : Model.Pcs.foldSt Wl [] Wl.runningQuad = (Wl, []) := by
  simp [Model.Pcs.foldSt]

theorem levelsFrom_eq (s : MachineState) (x : LCtx) {ℓ : ℕ} (Wl : Model.Pcs.WhirLocals)
    (hℓ : ℓ < K0 s + 2) :
    levelsFrom s x ℓ Wl = Model.Pcs.TM.loopN Model.Pcs.foldRoundRust (fcOf s ℓ - 0)
      (Model.Pcs.foldSt Wl [] Wl.runningQuad) >>= AFk s x ℓ := by
  rw [levelsFrom, zip_drop s hℓ, Model.Pcs.whirLevels_cons, foldSt_nil, Nat.sub_zero]

/-! ## The rounds' writes -/

/-- From the head `h` on: the slots `S - 856`, `S - 832`..`S - 816`, `S - 792`..`S - 776`, the
folds' header, `S - 640`..`S - 104`, the callees' stacks, `NEXT`, the heap allocated since `h`,
the folds' buffer at `h`, the sponge and offsets. -/
def FW (s h : MachineState) (hi a : Word) : Prop :=
  Within a (s.getReg .x2 - 856) 8 ∨ Within a (s.getReg .x2 - 832) 16 ∨
    Within a (s.getReg .x2 - 792) 16 ∨ Within a (s.getReg .x2 - 688) 24 ∨
    Within a (s.getReg .x2 - 640) 536 ∨ Within a (s.getReg .x2 - 2464) 1424 ∨
    Within a nextAddr 8 ∨ (heapNext h ≤ a.toNat ∧ a.toNat < hi.toNat) ∨ W s a ∨
    Within a (vecPtr h (s.getReg .x2 - 688)) ((vecCap h (s.getReg .x2 - 688)).toNat * 24)

theorem FW.mono {s h : MachineState} {hi hi' a : Word} (hle : hi.toNat ≤ hi'.toNat)
    (ha : FW s h hi a) : FW s h hi' a := by
  rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha.1, by omega⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ha))))))))

/-- The head's facts the rounds use. -/
structure HeadFacts (s : MachineState) (x : LCtx) (h : MachineState) : Prop where
  hs : heapNext s ≤ x.L
  hL : x.L ≤ heapNext h
  hend : heapNext h ≤ heapEnd
  fp : heapNext s ≤ x.FP.toNat ∧ x.FP.toNat + 8 * (K0 s + 2) ≤ x.L ∧ x.FP.toNat % 8 = 0
  rp : heapNext s ≤ x.RP.toNat ∧ x.RP.toNat + 8 * (K0 s + 2) ≤ x.L ∧ x.RP.toNat % 8 = 0
  F : (vecCap h (s.getReg .x2 - 688)).toNat * 24 = 0 ∨
    x.L ≤ (vecPtr h (s.getReg .x2 - 688)).toNat ∧
      (vecPtr h (s.getReg .x2 - 688)).toNat + (vecCap h (s.getReg .x2 - 688)).toNat * 24 ≤
        heapNext h

theorem Head.facts {s : MachineState} {x : LCtx} {h : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} (hh : Head s x h ℓ Wl) : HeadFacts s x h := by
  have hc := hh.cfg
  have hm := hh.mark
  have hb := hc.bufs
  have hn := hc.nxs
  have hF := hh.folds
  have hraw := hF.vec.raw
  simp only [RawVecOk, Buf] at hraw
  refine ⟨by omega, Nat.le_trans hm.2.2.2 hh.mono, hh.heap.hi, ⟨by omega, hm.1, hb.2.2.1⟩,
    ⟨by omega, hm.2.1, hb.2.2.2.2.2⟩, ?_⟩
  rcases hF.lo with h0 | h0
  · exact Or.inl (by rw [h0]; rfl)
  · rcases hraw.2 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨h0, h1.2⟩

/-- The function's invariant after the rounds' writes. -/
theorem FW.inv {s : MachineState} {x : LCtx} {h u : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} (hpre : VsoPre s) (hh : Head s x h ℓ Wl)
    (hfr : DFrame h u (FW s h (u.getMem nextAddr))) (hheap : HeapOk u)
    (hmono : heapNext h ≤ heapNext u) (hsp : u.getReg .x2 = h.getReg .x2) :
    InvR s u (u.getMem nextAddr) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hf := hh.facts
  have hi := LM.inv hpre hh.cfg.inv (by have := hf.hs; omega) hh.fr hh.heap hh.mono
    (hh.sp.trans hh.cfg.inv.sp.symm)
  have hhi := hheap.hi
  have hFh := hf.F
  refine Inv.step' hpre hi hfr (fun a ha ↦ ?_) (fun a ha ↦ ?_) rfl hmono hhi hsp
  · rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr ⟨by have := hf.hs; have := hf.hL; omega, ha.2⟩))
    · exact Or.inl (Or.inl ha)
    · refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩)) <;> rcases hFh with h0 | h0
      · simp only [Within] at ha; omega
      · have := hf.hs; simp only [Within] at ha; omega
      · simp only [Within] at ha; omega
      · simp only [Within, heapNext] at ha hmono h0 ⊢; omega
  · rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb, hnx]
    · addr_omega [ha.2, hb, hhi]
    · have hI := hpre.self
      have hS := Region.bounds hI.ok.self
      have hIs := hI.stack
      rw [stackLo_vso, vso_stack] at hIs
      simp only [W] at ha; addr_omega [ha, hIs, hS, hb]
    · have := hf.hend
      rcases hFh with h0 | h0
      · simp only [Within] at ha; omega
      · addr_omega [ha, h0.2, this, hb]

/-- The rounds' writes but the sponge are in `NS`. -/
theorem FW.ns {s : MachineState} {x : LCtx} {h : MachineState} {hi a : Word}
    (hpre : VsoPre s) (hf : HeadFacts s x h) (hhi : hi.toNat ≤ heapEnd) (ha : FW s h hi a)
    (hW : ¬ W s a) : NS s a := by
  have hb := bounds hpre
  rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ⟨by have := hf.hs; have := hf.hL; omega, by omega⟩))
  · exact absurd ha hW
  · have := hf.hs
    have := hf.hend
    rcases hf.F with h0 | h0
    · simp only [Within] at ha; omega
    · exact Or.inr (Or.inr (Or.inl ⟨by simp only [Within] at ha; omega,
        by simp only [Within] at ha; omega⟩))

/-- The rounds' writes miss the root. -/
theorem FW.root {s : MachineState} {x : LCtx} {h : MachineState} {hi : Word}
    (hpre : VsoPre s) (hf : HeadFacts s x h) (hhi : hi.toNat ≤ heapEnd) :
    ∀ y, Within y (s.getReg .x11) 32 → ¬ FW s h hi y := by
  have hb := bounds hpre
  have hr := hpre.root
  have hrs := hpre.rootSponge
  have hst := hr.stack
  have hfr := hr.free
  obtain ⟨hnx, -⟩ := sfacts hpre
  rw [stackLo_vso, vso_stack] at hst
  simp only [Outside] at hfr
  have := hf.hs
  have := hf.hL
  have := hf.hend
  intro y hy ha
  rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha
  · addr_omega [hy, ha, hst, hb]
  · addr_omega [hy, ha, hst, hb]
  · addr_omega [hy, ha, hst, hb]
  · addr_omega [hy, ha, hst, hb]
  · addr_omega [hy, ha, hst, hb]
  · addr_omega [hy, ha, hst, hb]
  · addr_omega [hy, ha, hfr.2]
  · rcases hfr.1 with h1 | h1
    · addr_omega [hy, ha.1, h1, hf.hs, hf.hL]
    · addr_omega [hy, ha.2, h1, hhi]
  · simp only [W] at ha; addr_omega [hy, ha, hrs]
  · rcases hf.F with h0 | h0
    · simp only [Within] at ha; omega
    · rcases hfr.1 with h1 | h1
      · addr_omega [hy, ha, h1, h0.1, hf.hs]
      · addr_omega [hy, ha, h1, h0.2, hf.hend]

/-! ## Steps that keep the mirror -/

theorem Runs.keep {s u v : MachineState} {ℓ : ℕ} {m : Model.TM Unit} {nx : Word}
    {X : Word → Prop} (hpre : VsoPre s) (h : Runs s u ℓ m) (hinv : InvR s u nx)
    (hX : DFrame u v X) (hXs : ∀ a, X a → NS s a)
    (hr : ∀ y, Within y (s.getReg .x11) 32 → ¬ X y) : Runs s v ℓ m :=
  h.step (digest_keep hX (root_bound hpre) hr) fun T hT ↦
    ⟨T, rfl, tr_keep hpre hinv hT hX hXs, rfl, rfl, rfl⟩

/-- A block writing the frame below the saved registers keeps the mirror. -/
theorem Runs.keepStk {s u v : MachineState} {ℓ : ℕ} {m : Model.TM Unit} {nx : Word}
    {X : Word → Prop} (hpre : VsoPre s) (h : Runs s u ℓ m) (hinv : InvR s u nx)
    (hX : DFrame u v X) (hXs : ∀ a, X a → Within a (s.getReg .x2 - 1040) 936) :
    Runs s v ℓ m := by
  have hb := bounds hpre
  have hrs := hpre.root.stack
  rw [stackLo_vso, vso_stack] at hrs
  exact h.keep hpre hinv hX (fun a ha ↦ Or.inl (by have := hXs a ha; addr_omega [this, hb]))
    fun y hy ha ↦ by have := hXs y ha; addr_omega [this, hy, hrs, hb]

theorem ofNat_toNat_eq {w : Word} {n : ℕ} (h : w.toNat = n) : w = BitVec.ofNat 64 n := by
  rw [← h]; simp

/-! ## The rounds' invariant -/

/-- Through a round of level `ℓ` (head `h`): `folds` holding `fl` (in the head's buffer or a new
one), `level_folds` holding `lfs` (in a new one), the quadratic `q` (the head's or a new one),
the three buffers apart. -/
structure RB (s : MachineState) (x : LCtx) (h u : MachineState) (ℓ : ℕ)
    (Wl : Model.Pcs.WhirLocals) (fl lfs q : List E) : Prop where
  head : Head s x h ℓ Wl
  fr : DFrame h u (FW s h (u.getMem nextAddr))
  heap : HeapOk u
  mono : heapNext h ≤ heapNext u
  sp : u.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040
  x9 : u.getReg .x9 = x.FP
  x18 : u.getReg .x18 = BitVec.ofNat 64 (24 * Wl.folds.length)
  x25 : u.getReg .x25 = s.getReg .x10 + 8
  x26 : u.getReg .x26 = s.getReg .x12
  x27 : u.getReg .x27 = s.getReg .x10
  m184 : u.getMem (s.getReg .x2 - 856) = BitVec.ofNat 64 ℓ
  m208 : u.getMem (s.getReg .x2 - 832) = BitVec.ofNat 64 (8 * ℓ)
  m216 : u.getMem (s.getReg .x2 - 824) = BitVec.ofNat 64 (rtOf s ℓ)
  m248 : u.getMem (s.getReg .x2 - 792) = BitVec.ofNat 64 (Wl.folds.length + 1)
  m256 : u.getMem (s.getReg .x2 - 784) = BitVec.ofNat 64 (fcOf s ℓ)
  F : VecOk u (s.getReg .x2 - 688) 24 8 ∧ vecEs u (s.getReg .x2 - 688) = fl ∧
    ((vecPtr u (s.getReg .x2 - 688) = vecPtr h (s.getReg .x2 - 688) ∧
      vecCap u (s.getReg .x2 - 688) = vecCap h (s.getReg .x2 - 688)) ∨
    NewBuf h u (vecPtr u (s.getReg .x2 - 688)) ((vecCap u (s.getReg .x2 - 688)).toNat * 24) 8)
  LF : VecOk u (s.getReg .x2 - 640) 24 8 ∧ vecEs u (s.getReg .x2 - 640) = lfs ∧
    NewBuf h u (vecPtr u (s.getReg .x2 - 640)) ((vecCap u (s.getReg .x2 - 640)).toNat * 24) 8
  Q : eListAt u (u.getReg .x22) (u.getReg .x23).toNat = q ∧ (u.getReg .x22).toNat % 8 = 0 ∧
    ((u.getReg .x22 = h.getReg .x22 ∧ u.getReg .x23 = h.getReg .x23) ∨
      (u.getReg .x23).toNat = 0 ∨ heapNext h ≤ (u.getReg .x22).toNat ∧
        (u.getReg .x22).toNat + 24 * (u.getReg .x23).toNat ≤ heapNext u)
  ap : Apart (vecPtr u (s.getReg .x2 - 688)) ((vecCap u (s.getReg .x2 - 688)).toNat * 24)
      (vecPtr u (s.getReg .x2 - 640)) ((vecCap u (s.getReg .x2 - 640)).toNat * 24) ∧
    Apart (vecPtr u (s.getReg .x2 - 688)) ((vecCap u (s.getReg .x2 - 688)).toNat * 24)
      (u.getReg .x22) (24 * (u.getReg .x23).toNat) ∧
    Apart (vecPtr u (s.getReg .x2 - 640)) ((vecCap u (s.getReg .x2 - 640)).toNat * 24)
      (u.getReg .x22) (24 * (u.getReg .x23).toNat)

/-- At `0x8000a1e8`, before round `j` of level `ℓ` (head `h`): `lf` drawn, the quadratic `q`. -/
structure Rnd (s : MachineState) (x : LCtx) (h u : MachineState) (ℓ : ℕ)
    (Wl : Model.Pcs.WhirLocals) (j : ℕ) (lf q : List E) : Prop
    extends RB s x h u ℓ Wl (Wl.folds ++ lf) lf q where
  pc : u.pc = 0x8000a1e8
  x6 : u.getReg .x6 = BitVec.ofNat 64 Wl.folds.length
  x19 : u.getReg .x19 = vecPtr u (s.getReg .x2 - 640)
  x20 : u.getReg .x20 = BitVec.ofNat 64 (24 * j)
  x21 : u.getReg .x21 = BitVec.ofNat 64 j
  jlt : j < fcOf s ℓ
  lfl : lf.length = j
  value : Runs s u ℓ (Model.Pcs.TM.loopN Model.Pcs.foldRoundRust (fcOf s ℓ - j)
    (Model.Pcs.foldSt Wl lf q) >>= AFk s x ℓ)

theorem vec_small {u : MachineState} {A : Word} {size : ℕ}
    (hv : VecOk u A size 8) (hh : HeapOk u) :
    (vecLen u A).toNat ≤ (vecCap u A).toNat ∧ (vecCap u A).toNat * size < 2 ^ 31 := by
  have hl := hv.len
  have hr := hv.raw
  have hhi := hh.hi
  simp only [RawVecOk, Buf, heapEnd] at hr hhi
  refine ⟨hl, ?_⟩
  rcases hr.2 with h0 | h0
  · omega
  · omega

/-- The ladders' words at the head. -/
theorem Head.words {s : MachineState} {x : LCtx} {h : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} (hpre : VsoPre s) (hh : Head s x h ℓ Wl) :
    h.getMem (x.FP + BitVec.ofNat 64 (8 * ℓ)) = BitVec.ofNat 64 (fcOf s ℓ) ∧
      h.getMem (x.RP + BitVec.ofNat 64 (8 * ℓ)) = BitVec.ofNat 64 (rtOf s ℓ) := by
  have hf := hh.facts
  have hc := hh.cfg
  have hend := (hc.inv.heap hpre.heap).hi
  have hL : x.L ≤ heapEnd := by have := hh.mark.2.2.2; omega
  have hwF := LM.words hpre hh.fr hf.fp.1 hf.fp.2.1 hL
  have hwR := LM.words hpre hh.fr hf.rp.1 hf.rp.2.1 hL
  rw [hc.folds] at hwF
  rw [hc.rates] at hwR
  rw [readWords_get hwF hh.lvl, readWords_get hwR hh.lvl, lw_getD, lw_getD]
  exact ⟨rfl, rfl⟩

theorem Head.invR {s : MachineState} {x : LCtx} {h : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} (hpre : VsoPre s) (hh : Head s x h ℓ Wl) :
    InvR s h (h.getMem nextAddr) :=
  LM.inv hpre hh.cfg.inv (by have := hh.facts.hs; omega) hh.fr hh.heap hh.mono
    (hh.sp.trans hh.cfg.inv.sp.symm)

/-- A `Vec<E>` whose header and elements a frame misses. -/
theorem vecE_keep {u v : MachineState} {A : Word} {X : Word → Prop} (hX : DFrame u v X)
    (hv : VecOk u A 24 8)
    (hm : ∀ a, X a → ¬ Within a A 24 ∧ ¬ Within a (vecPtr u A) ((vecCap u A).toNat * 24))
    (hA : A.toNat + 24 ≤ 2 ^ 64) (hmono : heapNext u ≤ heapNext v) (hh : HeapOk u) :
    VecOk v A 24 8 ∧ vecEs v A = vecEs u A ∧ vecPtr v A = vecPtr u A ∧
      vecCap v A = vecCap u A ∧ vecLen v A = vecLen u A := by
  have w (o : Nat) (ho : o + 8 ≤ 24) :
      v.getMem (A + BitVec.ofNat 64 o) = u.getMem (A + BitVec.ofNat 64 o) :=
    hX _ fun i hi hw ↦ (hm _ hw).1 (by addr_omega [hi, ho, hA])
  have e0 : vecCap v A = vecCap u A := by
    have := w 0 (by decide); simp only [add_ofNat_zero] at this; exact this
  have e1 : vecPtr v A = vecPtr u A := w 8 (by decide)
  have e2 : vecLen v A = vecLen u A := w 16 (by decide)
  have hsm := vec_small hv hh
  have hraw := hv.raw
  simp only [RawVecOk, Buf] at hraw
  refine ⟨⟨?_, by rw [e0, e2]; exact hv.len⟩, ?_, e1, e0, e2⟩
  · simp only [RawVecOk, Buf]
    rw [e0, e1]
    refine ⟨hraw.1, ?_⟩
    rcases hraw.2 with h0 | h0
    · exact Or.inl h0
    · exact Or.inr ⟨h0.1, by omega⟩
  · simp only [vecEs, e1, e2]
    have hl := hv.len
    refine DFrame.eList hX (fun y hy hw ↦ (hm _ hw).2 (by simp only [Within] at hy ⊢; omega)) ?_
    rcases hraw.2 with h0 | h0
    · left; omega
    · right; have := hh.hi; simp only [heapEnd] at this; omega

/-- Where the round's three buffers lie. -/
structure RB.Bufs (s : MachineState) (x : LCtx) (u : MachineState) : Prop where
  F : (vecCap u (s.getReg .x2 - 688)).toNat * 24 = 0 ∨ x.L ≤ (vecPtr u (s.getReg .x2 - 688)).toNat ∧
    (vecPtr u (s.getReg .x2 - 688)).toNat + (vecCap u (s.getReg .x2 - 688)).toNat * 24 ≤ heapNext u
  LF : (vecCap u (s.getReg .x2 - 640)).toNat * 24 = 0 ∨
    x.L ≤ (vecPtr u (s.getReg .x2 - 640)).toNat ∧
    (vecPtr u (s.getReg .x2 - 640)).toNat + (vecCap u (s.getReg .x2 - 640)).toNat * 24 ≤ heapNext u
  Q : 24 * (u.getReg .x23).toNat = 0 ∨ x.L ≤ (u.getReg .x22).toNat ∧
    (u.getReg .x22).toNat + 24 * (u.getReg .x23).toNat ≤ heapNext u

theorem RB.bufs {s : MachineState} {x : LCtx} {h u : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {fl lfs q : List E} (hr : RB s x h u ℓ Wl fl lfs q) :
    RB.Bufs s x u := by
  have hf := hr.head.facts
  have hL := hf.hL
  have hm := hr.mono
  refine ⟨?_, ?_, ?_⟩
  · rcases hr.F.2.2 with ⟨e1, e2⟩ | h0
    · rw [e1, e2]
      rcases hf.F with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨h1.1, by omega⟩
    · rcases h0.2 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨by omega, h1.2⟩
  · rcases hr.LF.2.2.2 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨by omega, h1.2⟩
  · rcases hr.Q.2.2 with ⟨e1, e2⟩ | h0 | h0
    · rw [e1, e2]
      rcases hr.head.quad.2.2 with h1 | h1
      · exact Or.inl (by omega)
      · exact Or.inr ⟨h1.1, by omega⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, h0.2⟩

/-- The round's slots: `S - 856`, `S - 832`..`S - 816`, `S - 792`..`S - 776`, the two headers. -/
@[rv_addr] def RSlots (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 856) 8 ∨ Within a (s.getReg .x2 - 832) 16 ∨
    Within a (s.getReg .x2 - 792) 16 ∨ Within a (s.getReg .x2 - 688) 24 ∨
    Within a (s.getReg .x2 - 640) 24

/-- The round's three buffers. -/
@[rv_addr] def RBufs (s u : MachineState) (a : Word) : Prop :=
  Within a (vecPtr u (s.getReg .x2 - 688)) ((vecCap u (s.getReg .x2 - 688)).toNat * 24) ∨
    Within a (vecPtr u (s.getReg .x2 - 640)) ((vecCap u (s.getReg .x2 - 640)).toNat * 24) ∨
    Within a (u.getReg .x22) (24 * (u.getReg .x23).toNat)

/-- A step that misses the round's slots and buffers keeps it. -/
theorem RB.carry {s : MachineState} {x : LCtx} {h u v : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {fl lfs q : List E} {X : Word → Prop} (hpre : VsoPre s)
    (hr : RB s x h u ℓ Wl fl lfs q) (hX : DFrame u v X)
    (hXs : ∀ a, X a → FW s h (v.getMem nextAddr) a)
    (hXm : ∀ a, X a → ¬ RSlots s a ∧ ¬ RBufs s u a) (hheap : HeapOk v)
    (hmono : heapNext u ≤ heapNext v)
    (hreg : ∀ r ∈ [Reg.x2, .x9, .x18, .x22, .x23, .x25, .x26, .x27], v.getReg r = u.getReg r) :
    RB s x h v ℓ Wl fl lfs q := by
  have hb := bounds hpre
  have hu := hr.heap
  have hw (y : Word) (hy : Within y (s.getReg .x2 - 856) 8 ∨ Within y (s.getReg .x2 - 832) 16 ∨
      Within y (s.getReg .x2 - 792) 16) (hy8 : ∀ i < 8, Within (y + BitVec.ofNat 64 i)
        (s.getReg .x2 - 856) 8 ∨ Within (y + BitVec.ofNat 64 i) (s.getReg .x2 - 832) 16 ∨
        Within (y + BitVec.ofNat 64 i) (s.getReg .x2 - 792) 16) : v.getMem y = u.getMem y :=
    hX y fun i hi hx ↦ (hXm _ hx).1 (by
      rcases hy8 i hi with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inl h1)))
  have hFk := vecE_keep hX hr.F.1 (fun a ha ↦ ⟨fun hw ↦ (hXm a ha).1 (Or.inr (Or.inr (Or.inr
      (Or.inl hw)))), fun hw ↦ (hXm a ha).2 (Or.inl hw)⟩) (by addr_omega [hb]) hmono hu
  have hLk := vecE_keep hX hr.LF.1 (fun a ha ↦ ⟨fun hw ↦ (hXm a ha).1 (Or.inr (Or.inr (Or.inr
      (Or.inr hw)))), fun hw ↦ (hXm a ha).2 (Or.inr (Or.inl hw))⟩) (by addr_omega [hb]) hmono hu
  have r22 := hreg .x22 (by decide)
  have r23 := hreg .x23 (by decide)
  have hB := hr.bufs
  have hq := hr.Q
  have nb {p p' : Word} {n n' : ℕ} (e1 : p' = p) (e2 : n' = n) (hn : NewBuf h u p n 8) :
      NewBuf h v p' n' 8 := by
    subst e1; subst e2
    exact ⟨hn.1, by rcases hn.2 with h0 | h0; exact Or.inl h0; exact Or.inr ⟨h0.1, by omega⟩⟩
  refine {
    head := hr.head
    fr := (hr.fr.mono fun a ha ↦ FW.mono (by simp only [heapNext] at hmono; exact hmono) ha).trans
      hX hXs
    heap := hheap
    mono := Nat.le_trans hr.mono hmono
    sp := by rw [hreg .x2 (by decide), hr.sp]
    x9 := by rw [hreg .x9 (by decide), hr.x9]
    x18 := by rw [hreg .x18 (by decide), hr.x18]
    x25 := by rw [hreg .x25 (by decide), hr.x25]
    x26 := by rw [hreg .x26 (by decide), hr.x26]
    x27 := by rw [hreg .x27 (by decide), hr.x27]
    m184 := by rw [hw _ (Or.inl (by addr_omega [hb])) fun i hi ↦ Or.inl (by addr_omega [hi, hb])]
               exact hr.m184
    m208 := by rw [hw _ (Or.inr (Or.inl (by addr_omega [hb])))
                 fun i hi ↦ Or.inr (Or.inl (by addr_omega [hi, hb]))]
               exact hr.m208
    m216 := by rw [hw _ (Or.inr (Or.inl (by addr_omega [hb])))
                 fun i hi ↦ Or.inr (Or.inl (by addr_omega [hi, hb]))]
               exact hr.m216
    m248 := by rw [hw _ (Or.inr (Or.inr (by addr_omega [hb])))
                 fun i hi ↦ Or.inr (Or.inr (by addr_omega [hi, hb]))]
               exact hr.m248
    m256 := by rw [hw _ (Or.inr (Or.inr (by addr_omega [hb])))
                 fun i hi ↦ Or.inr (Or.inr (by addr_omega [hi, hb]))]
               exact hr.m256
    F := ⟨hFk.1, by rw [hFk.2.1]; exact hr.F.2.1, by
      rw [hFk.2.2.1, hFk.2.2.2.1]
      rcases hr.F.2.2 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (nb rfl rfl h0)⟩
    LF := ⟨hLk.1, by rw [hLk.2.1]; exact hr.LF.2.1, by
      rw [hLk.2.2.1, hLk.2.2.2.1]; exact nb rfl rfl hr.LF.2.2⟩
    Q := ⟨by
        rw [r22, r23, ← hq.1]
        rcases hB.Q with h0 | h0
        · have : (u.getReg .x23).toNat = 0 := by omega
          rw [this]; rfl
        · exact hX.eList (fun y hy hx ↦ (hXm _ hx).2 (Or.inr (Or.inr hy)))
            (Or.inr (by have := hu.hi; simp only [heapEnd] at this; omega)),
      by rw [r22]; exact hq.2.1, by
        rw [r22, r23]
        rcases hq.2.2 with h0 | h0 | h0
        · exact Or.inl h0
        · exact Or.inr (Or.inl h0)
        · exact Or.inr (Or.inr ⟨h0.1, by omega⟩)⟩
    ap := by rw [hFk.2.2.1, hFk.2.2.2.1, hLk.2.2.1, hLk.2.2.2.1, r22, r23]; exact hr.ap }

/-- A step that writes the folds or `level_folds` (headers and buffers), given what they then
hold, and misses the other slots and the quadratic. -/
theorem RB.carry2 {s : MachineState} {x : LCtx} {h u v : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {fl lfs q fl' lfs' : List E} {X : Word → Prop} (hpre : VsoPre s)
    (hr : RB s x h u ℓ Wl fl lfs q) (hX : DFrame u v X)
    (hXs : ∀ a, X a → FW s h (v.getMem nextAddr) a)
    (hXm : ∀ a, X a → ¬ (Within a (s.getReg .x2 - 856) 8 ∨ Within a (s.getReg .x2 - 832) 16 ∨
      Within a (s.getReg .x2 - 792) 16) ∧ ¬ Within a (u.getReg .x22) (24 * (u.getReg .x23).toNat))
    (hheap : HeapOk v) (hmono : heapNext u ≤ heapNext v)
    (hreg : ∀ r ∈ [Reg.x2, .x9, .x18, .x22, .x23, .x25, .x26, .x27], v.getReg r = u.getReg r)
    (hF : VecOk v (s.getReg .x2 - 688) 24 8 ∧ vecEs v (s.getReg .x2 - 688) = fl' ∧
      ((vecPtr v (s.getReg .x2 - 688) = vecPtr h (s.getReg .x2 - 688) ∧
        vecCap v (s.getReg .x2 - 688) = vecCap h (s.getReg .x2 - 688)) ∨
      NewBuf h v (vecPtr v (s.getReg .x2 - 688)) ((vecCap v (s.getReg .x2 - 688)).toNat * 24) 8))
    (hLF : VecOk v (s.getReg .x2 - 640) 24 8 ∧ vecEs v (s.getReg .x2 - 640) = lfs' ∧
      NewBuf h v (vecPtr v (s.getReg .x2 - 640)) ((vecCap v (s.getReg .x2 - 640)).toNat * 24) 8)
    (hap : Apart (vecPtr v (s.getReg .x2 - 688)) ((vecCap v (s.getReg .x2 - 688)).toNat * 24)
      (vecPtr v (s.getReg .x2 - 640)) ((vecCap v (s.getReg .x2 - 640)).toNat * 24) ∧
      Apart (vecPtr v (s.getReg .x2 - 688)) ((vecCap v (s.getReg .x2 - 688)).toNat * 24)
        (u.getReg .x22) (24 * (u.getReg .x23).toNat) ∧
      Apart (vecPtr v (s.getReg .x2 - 640)) ((vecCap v (s.getReg .x2 - 640)).toNat * 24)
        (u.getReg .x22) (24 * (u.getReg .x23).toNat)) :
    RB s x h v ℓ Wl fl' lfs' q := by
  have hb := bounds hpre
  have hu := hr.heap
  have hw (y : Word) (hy8 : ∀ i < 8, Within (y + BitVec.ofNat 64 i)
        (s.getReg .x2 - 856) 8 ∨ Within (y + BitVec.ofNat 64 i) (s.getReg .x2 - 832) 16 ∨
        Within (y + BitVec.ofNat 64 i) (s.getReg .x2 - 792) 16) : v.getMem y = u.getMem y :=
    hX y fun i hi hx ↦ (hXm _ hx).1 (hy8 i hi)
  have r22 := hreg .x22 (by decide)
  have r23 := hreg .x23 (by decide)
  have hB := hr.bufs
  have hq := hr.Q
  refine {
    head := hr.head
    fr := (hr.fr.mono fun a ha ↦ FW.mono (by simp only [heapNext] at hmono; exact hmono) ha).trans
      hX hXs
    heap := hheap
    mono := Nat.le_trans hr.mono hmono
    sp := by rw [hreg .x2 (by decide), hr.sp]
    x9 := by rw [hreg .x9 (by decide), hr.x9]
    x18 := by rw [hreg .x18 (by decide), hr.x18]
    x25 := by rw [hreg .x25 (by decide), hr.x25]
    x26 := by rw [hreg .x26 (by decide), hr.x26]
    x27 := by rw [hreg .x27 (by decide), hr.x27]
    m184 := by rw [hw _ fun i hi ↦ Or.inl (by addr_omega [hi, hb])]; exact hr.m184
    m208 := by rw [hw _ fun i hi ↦ Or.inr (Or.inl (by addr_omega [hi, hb]))]; exact hr.m208
    m216 := by rw [hw _ fun i hi ↦ Or.inr (Or.inl (by addr_omega [hi, hb]))]; exact hr.m216
    m248 := by rw [hw _ fun i hi ↦ Or.inr (Or.inr (by addr_omega [hi, hb]))]; exact hr.m248
    m256 := by rw [hw _ fun i hi ↦ Or.inr (Or.inr (by addr_omega [hi, hb]))]; exact hr.m256
    F := hF
    LF := hLF
    Q := ⟨by
        rw [r22, r23, ← hq.1]
        rcases hB.Q with h0 | h0
        · have : (u.getReg .x23).toNat = 0 := by omega
          rw [this]; rfl
        · exact hX.eList (fun y hy hx ↦ (hXm _ hx).2 hy)
            (Or.inr (by have := hu.hi; simp only [heapEnd] at this; omega)),
      by rw [r22]; exact hq.2.1, by
        rw [r22, r23]
        rcases hq.2.2 with h0 | h0 | h0
        · exact Or.inl h0
        · exact Or.inr (Or.inl h0)
        · exact Or.inr (Or.inr ⟨h0.1, by omega⟩)⟩
    ap := by rw [r22, r23]; exact hap }

theorem NewBuf.widen {h u v : MachineState} {p : Word} {n : ℕ} (hn : NewBuf u v p n 8)
    (hle : heapNext h ≤ heapNext u) : NewBuf h v p n 8 :=
  ⟨hn.1, by rcases hn.2 with h0 | h0; exact Or.inl h0; exact Or.inr ⟨by omega, h0.2⟩⟩

theorem NewBuf.grow {h u v : MachineState} {p : Word} {n : ℕ} (hn : NewBuf h u p n 8)
    (hle : heapNext u ≤ heapNext v) : NewBuf h v p n 8 :=
  ⟨hn.1, by rcases hn.2 with h0 | h0; exact Or.inl h0; exact Or.inr ⟨h0.1, by omega⟩⟩

/-- One `E` pushed: the length at `A + 16`, the element after the old ones. -/
theorem vecE_push {u v : MachineState} {A : Word} {X : Word → Prop} {xs : List E} {c : E}
    (hv : VecOk u A 24 8) (he : vecEs u A = xs) (hX : DFrame u v X)
    (hXm : ∀ a, X a → Within a (A + 16) 8 ∨
      Within a (vecPtr u A + BitVec.ofNat 64 (24 * xs.length)) 24)
    (hlt : xs.length < (vecCap u A).toNat)
    (hl : v.getMem (A + 16) = BitVec.ofNat 64 (xs.length + 1))
    (hc : eAt v (vecPtr u A + BitVec.ofNat 64 (24 * xs.length)) = c)
    (hA : heapEnd ≤ A.toNat) (hA' : A.toNat + 24 ≤ 2 ^ 64) (hh : HeapOk u)
    (hmono : heapNext u ≤ heapNext v) :
    VecOk v A 24 8 ∧ vecEs v A = xs ++ [c] ∧ vecPtr v A = vecPtr u A ∧
      vecCap v A = vecCap u A := by
  have hraw := hv.raw
  simp only [RawVecOk, Buf] at hraw
  have hbuf := hraw.2.resolve_left (by omega)
  have hhi := hh.hi
  have hlen : (vecLen u A).toNat = xs.length := by
    rw [← he]; simp only [vecEs, eListAt_length]
  have w0 : v.getMem A = u.getMem A := hX _ fun i hi hx ↦ by
    rcases hXm _ hx with hx | hx
    · addr_omega [hx, hi, hA']
    · addr_omega [hx, hi, hbuf, hlt, hhi, hA, hA']
  have w8 : v.getMem (A + 8) = u.getMem (A + 8) := hX _ fun i hi hx ↦ by
    rcases hXm _ hx with hx | hx
    · addr_omega [hx, hi, hA']
    · addr_omega [hx, hi, hbuf, hlt, hhi, hA, hA']
  have e0 : vecCap v A = vecCap u A := w0
  have e1 : vecPtr v A = vecPtr u A := w8
  have hsmall : xs.length + 1 < 2 ^ 64 := by omega
  have hlv : (vecLen v A).toNat = xs.length + 1 := by
    simp only [vecLen]; rw [hl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall]
  refine ⟨⟨?_, by rw [e0, hlv]; exact hlt⟩, ?_, e1, e0⟩
  · simp only [RawVecOk, Buf]
    rw [e0, e1]
    exact ⟨hraw.1, Or.inr ⟨hbuf.1, by omega⟩⟩
  · have hp : (vecPtr u A).toNat + 24 * xs.length ≤ 2 ^ 64 := by omega
    have hm : ∀ y, Within y (vecPtr u A) (24 * xs.length) → ¬ X y := fun y hy hx ↦ by
      simp only [Within] at hy
      rcases hXm _ hx with hx | hx
      · addr_omega [hx, hy.1, hy.2, hbuf, hlt, hhi, hA, hA']
      · addr_omega [hx, hy.1, hy.2, hbuf, hlt, hhi]
    have hrest : eListAt v (vecPtr u A) xs.length = xs := by
      rw [hX.eList hm (Or.inr hp), ← hlen]; exact he
    simp only [vecEs]
    rw [hlv, e1, Samples.eListAt_succ, hc, hrest]

/-- A step that misses the round's slots, given what the three buffers then hold. -/
theorem RB.carryQ {s : MachineState} {x : LCtx} {h u v : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {fl lfs q fl' lfs' q' : List E} {X : Word → Prop}
    (hpre : VsoPre s) (hr : RB s x h u ℓ Wl fl lfs q) (hX : DFrame u v X)
    (hXs : ∀ a, X a → FW s h (v.getMem nextAddr) a)
    (hXm : ∀ a, X a → ¬ (Within a (s.getReg .x2 - 856) 8 ∨ Within a (s.getReg .x2 - 832) 16 ∨
      Within a (s.getReg .x2 - 792) 16))
    (hheap : HeapOk v) (hmono : heapNext u ≤ heapNext v)
    (hreg : ∀ r ∈ [Reg.x2, .x9, .x18, .x25, .x26, .x27], v.getReg r = u.getReg r)
    (hF : VecOk v (s.getReg .x2 - 688) 24 8 ∧ vecEs v (s.getReg .x2 - 688) = fl' ∧
      ((vecPtr v (s.getReg .x2 - 688) = vecPtr h (s.getReg .x2 - 688) ∧
        vecCap v (s.getReg .x2 - 688) = vecCap h (s.getReg .x2 - 688)) ∨
      NewBuf h v (vecPtr v (s.getReg .x2 - 688)) ((vecCap v (s.getReg .x2 - 688)).toNat * 24) 8))
    (hLF : VecOk v (s.getReg .x2 - 640) 24 8 ∧ vecEs v (s.getReg .x2 - 640) = lfs' ∧
      NewBuf h v (vecPtr v (s.getReg .x2 - 640)) ((vecCap v (s.getReg .x2 - 640)).toNat * 24) 8)
    (hQ : eListAt v (v.getReg .x22) (v.getReg .x23).toNat = q' ∧ (v.getReg .x22).toNat % 8 = 0 ∧
      ((v.getReg .x22 = h.getReg .x22 ∧ v.getReg .x23 = h.getReg .x23) ∨
        (v.getReg .x23).toNat = 0 ∨ heapNext h ≤ (v.getReg .x22).toNat ∧
          (v.getReg .x22).toNat + 24 * (v.getReg .x23).toNat ≤ heapNext v))
    (hap : Apart (vecPtr v (s.getReg .x2 - 688)) ((vecCap v (s.getReg .x2 - 688)).toNat * 24)
      (vecPtr v (s.getReg .x2 - 640)) ((vecCap v (s.getReg .x2 - 640)).toNat * 24) ∧
      Apart (vecPtr v (s.getReg .x2 - 688)) ((vecCap v (s.getReg .x2 - 688)).toNat * 24)
        (v.getReg .x22) (24 * (v.getReg .x23).toNat) ∧
      Apart (vecPtr v (s.getReg .x2 - 640)) ((vecCap v (s.getReg .x2 - 640)).toNat * 24)
        (v.getReg .x22) (24 * (v.getReg .x23).toNat)) :
    RB s x h v ℓ Wl fl' lfs' q' := by
  have hb := bounds hpre
  have hw (y : Word) (hy8 : ∀ i < 8, Within (y + BitVec.ofNat 64 i)
        (s.getReg .x2 - 856) 8 ∨ Within (y + BitVec.ofNat 64 i) (s.getReg .x2 - 832) 16 ∨
        Within (y + BitVec.ofNat 64 i) (s.getReg .x2 - 792) 16) : v.getMem y = u.getMem y :=
    hX y fun i hi hx ↦ hXm _ hx (hy8 i hi)
  exact {
    head := hr.head
    fr := (hr.fr.mono fun a ha ↦ FW.mono (by simp only [heapNext] at hmono; exact hmono) ha).trans
      hX hXs
    heap := hheap
    mono := Nat.le_trans hr.mono hmono
    sp := by rw [hreg .x2 (by decide), hr.sp]
    x9 := by rw [hreg .x9 (by decide), hr.x9]
    x18 := by rw [hreg .x18 (by decide), hr.x18]
    x25 := by rw [hreg .x25 (by decide), hr.x25]
    x26 := by rw [hreg .x26 (by decide), hr.x26]
    x27 := by rw [hreg .x27 (by decide), hr.x27]
    m184 := by rw [hw _ fun i hi ↦ Or.inl (by addr_omega [hi, hb])]; exact hr.m184
    m208 := by rw [hw _ fun i hi ↦ Or.inr (Or.inl (by addr_omega [hi, hb]))]; exact hr.m208
    m216 := by rw [hw _ fun i hi ↦ Or.inr (Or.inl (by addr_omega [hi, hb]))]; exact hr.m216
    m248 := by rw [hw _ fun i hi ↦ Or.inr (Or.inr (by addr_omega [hi, hb]))]; exact hr.m248
    m256 := by rw [hw _ fun i hi ↦ Or.inr (Or.inr (by addr_omega [hi, hb]))]; exact hr.m256
    F := hF
    LF := hLF
    Q := hQ
    ap := hap }

end Rv64Verifier.Proofs.Pcs.Vso
