/-
  LeanVM.Guest.B1.KeccakGkr.LayerCA

  `keccak_layer`'s first sections, completely: the head, the product read and absorbed, the
  projection check, the grind and the squeeze of `s`, on the honest valuation.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerSecA
public import LeanVM.Guest.B1.KeccakGkr.LayerCBlock
public import LeanVM.Guest.B1.Bits.GrindFwd
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«keccak_layer__L»
import LeanVM.Guest.Data.ValNames.«keccak_layer__L0»
import LeanVM.Guest.Data.ValNames.«keccak_layer__L1»
import LeanVM.Guest.StmtsAppend

/-!
# The product and `s`, completely

`layerA_complete`: on a valuation satisfying the equations of `headT ++ prodT ++ checkT ++ sqT`,
with the waiting word's cells in the arguments, the claim's record, the product and the nonce in
memory (no store through `claim` or `cur`), the honest projection check, the nonce passing the
grind, a memory where the inlined `grind_check`'s range checks pass and the tables at `tabs`, no
store into its values and the oracle at its windows the honest ones, the four sections hold
(`sqT_complete`: the grind's word is the permutation's output `1`, `grindOk_iff`, and the inlined
`grind_check` holds, `gcInline_holds_of_good`). The residual atoms (`resid`: the claim's
and the stream's loads, the check) are kernel-checked lists.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {C : CallRel} {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

/-- The head and the product. -/
def secA1 (first : ℕ) : List Stmt := headT first ⧺ prodT (.n (valf% «keccak_layer» "cursor@1")) (muB first) (prodTab first)

/-- The check and the grind's squeeze. -/
def secA2 (first : ℕ) : List Stmt := checkT (accL first) ⧺ sqT first

/-- The residual atoms of the head and the product: the claim's weights, the stream words. -/
def residA1 (first : ℕ) : List Atom :=
  (List.range 16).map (fun i ↦ .load (.n (muB first + i)) (.n (valf% «keccak_layer» "claim")) (6 + i)) ++
    (List.range 47).map fun k ↦ .load (.n ((prodTab first).getD k default).a) (.n (valf% «keccak_layer» "cursor@1")) k

/-- The residual atoms of the check. -/
def residC (first : ℕ) : List Atom :=
  [.load (.n (accL first + 1)) (.n (valf% «keccak_layer» "claim")) 1, .load (.n (accL first + 4)) (.n (valf% «keccak_layer» "claim")) 0,
    .assertEq (.n (accL first + 3)) (.n (accL first + 4))]

theorem secA_atoms {first : ℕ} (hf : first < 2) :
    (secA1 first).all isAtom = true ∧ (checkT (accL first)).all isAtom = true := by
  interval_cases first
  · exact ⟨by decide +kernel, by decide +kernel⟩
  · exact ⟨by decide +kernel, by decide +kernel⟩

theorem secA_resid1 {first : ℕ} (hf : first < 2) : resid (atomsL (secA1 first)) = residA1 first := by
  interval_cases first
  · decide +kernel
  · decide +kernel

theorem secA_residC {first : ℕ} (hf : first < 2) :
    resid (atomsL (checkT (accL first))) = residC first := by
  interval_cases first
  · decide +kernel
  · decide +kernel

theorem prodTab_a_eq {first : ℕ} (hf : first < 2) {prod : List E} (hpl : prod.length = 47)
    (hr : ReadsAt rd (σ (.n (valf% «keccak_layer» "cursor@1"))) prod)
    (hr' : ReadsAt rd (σ (.n (valf% «keccak_layer» "cursor@1"))) ((prodTab first).map fun p ↦ σ (.n p.a))) :
    (prodTab first).map (fun p ↦ σ (.n p.a)) = prod := by
  obtain ⟨hl, -⟩ := prodTab_facts first hf
  apply List.ext_getElem (by simp [hl, hpl])
  intro k h1 h2
  exact loadHolds_unique (hr' k h1) (hr k h2)

/-- The permutation's output `1` of a grind's nonce: `grind_check`'s word. -/
theorem grind_cell {s : Fs} {n : E} {b : ℕ}
    (hout : ∀ k (hk : k < 13), σ (((List.range 13).map fun j ↦ V.n (b + j)).getD k default) =
      cellsOfState (s.nonceState n) false ⟨k, hk⟩)
    (hok : s.GrindOk sGrindBits n) : ((σ (.n (b + 1))).limb 0).lane.toNat % 2 ^ 3 = 0 := by
  have h1 := hout 1 (by omega)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by omega : 1 < 13), Option.map_some, Option.getD_some] at h1
  rw [sGrindBits_eq, grindOk_iff (by decide : (3 : ℕ) ≠ 0)] at hok
  rw [h1]
  exact hok

/-- The permutation's output `1` of a grind's nonce, as a cell. -/
theorem grind_out1 {s : Fs} {n : E} {b : ℕ}
    (hout : ∀ k (hk : k < 13), σ (((List.range 13).map fun j ↦ V.n (b + j)).getD k default) =
      cellsOfState (s.nonceState n) false ⟨k, hk⟩) :
    σ (.n (b + 1)) = cellsOfState (s.nonceState n) false ⟨1, by omega⟩ := by
  have h1 := hout 1 (by omega)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by omega : 1 < 13), Option.map_some, Option.getD_some] at h1
  exact h1

/-- **The grind and the squeeze, completely**: from the cells the product leaves, the nonce at
the cursor's word `47` passing the grind, and the inlined `grind_check`'s conditions, `sqT` holds. -/
theorem sqT_complete {first : ℕ} (hf : first < 2) {s : Fs} (hs : SpOk σ s (capF first, pendF first))
    (hg : ∀ st ∈ sqT first, GoodS rd S w σ st) (hS7 : ∀ d off, Atom.load d (.n (valf% «keccak_layer» "cursor@1")) off ∉ S)
    {n : E} (hn : LoadHolds rd (σ (.n (valf% «keccak_layer» "cursor@1"))) 47 n) (hok : s.GrindOk sGrindBits n)
    (hrc : ∀ v ≤ 11, ∀ e < 2 ^ v, ∃ y t1 t2 : E, LoadHolds rd (gen ^ e) 0 t1 ∧
      wBound v = gen ^ e * y ∧ LoadHolds rd y 0 t2)
    (ht : WinTabs rd (σ (.n (valf% «keccak_layer» "tabs"))))
    (hSg : ∀ a ∈ S, loadInto (layOff first + 544) (layOff first + 544 + (gcLen 3 - 2)) a = false)
    (hwin : ∀ j ≤ gcW 3, w (layOff first + 544 + j) =
      gcWin 3 (cellsOfState (s.nonceState n) false ⟨1, by omega⟩) j) :
    σ (.n (nonceV first)) = n ∧
      σ (.n (layOff first + 532)) = cellsOfState (s.nonceState n) false ⟨1, by omega⟩ ∧
      s.grindSqueeze sGrindBits n =
        (σ (.n (layOff first + 531)), ⟨(cap5 (layOff first + 539)).map σ, []⟩) ∧
      ∀ {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList C rd σ (sqT first) next kret := by
  interval_cases first
  · have g1 : ∀ st ∈ fsNonceT (.n (valf% «keccak_layer» "cursor@1")) 47 529, GoodS rd S w σ st := fun st h ↦
      hg st (by simp [sqT, h])
    have gk : Good rd S w σ (.keccak (sqIns 0) ((List.range 13).map fun k ↦ .n (532 + k))
        false false) := hg (.atom (.keccak (sqIns 0) ((List.range 13).map fun k ↦ .n (532 + k))
        false false)) (by simp [sqT, keccakA])
    have e528 : σ (.n 529) = n := load_val (w := w) (g1 _ (List.mem_cons_self ..)) (hS7 _ _) hn
    have hp : FsPackOk σ (.n 529) (529 + 1) dsPowNonce :=
      fsPack_vals_of_good fun st h ↦ g1 st (List.mem_cons_of_mem _ h)
    have hk := keccakA_complete gk
    have hlen := pendOk_length hs.2
    have hs' : SpOk σ (s.absorb (σ (.n 529)) dsPowNonce)
        (capF 0, pendF 0 ++ [(.n 530, .n 531)]) := by
      have hne : s.pend.length ≠ rateScalars := by rw [hlen]; decide
      simp only [Fs.absorb, hne, ↓reduceIte]
      exact ⟨hs.1, pendOk_append hs.2 (fsPackT_cells hp)⟩
    obtain ⟨-, hout⟩ := spOk_perm hs' hk (zs := []) (by decide) rfl (by decide)
    rw [e528] at hout
    have hpow := grind_cell (s := s) (b := 532) hout hok
    obtain ⟨-, hsq⟩ := grind_sq (s := s) (n := n) (b := 532) hout hpow
    have h533 : σ (.n (val% «keccak_layer__L0» "nxt[1]@12")) = cellsOfState (s.nonceState n) false ⟨1, by omega⟩ := grind_out1 hout
    refine ⟨e528, grind_out1 hout, hsq, fun {next kret} hnx ↦ ?_⟩
    have hgi : ∀ st ∈ gcInlineT 3 (val% «keccak_layer__L0» "wins[0]") (.n (val% «keccak_layer__L0» "nxt[1]@12")) (.n (valf% «keccak_layer» "tabs")), GoodS rd S w σ st :=
      fun st h ↦ hg st (by
        simp only [sqT, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte]
        exact List.mem_append_right _ h)
    have HG : Stmt.HoldsList C rd σ (gcInlineT 3 (val% «keccak_layer__L0» "wins[0]") (.n (val% «keccak_layer__L0» "nxt[1]@12")) (.n (valf% «keccak_layer» "tabs"))) next kret :=
      gcInline_holds_of_good (by decide) (by decide) (by decide) hgi hSg hrc ht
        (fun j hj ↦ by rw [h533]; exact hwin j hj) hpow hnx
    simp only [sqT, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte, holdsList_append, holds_fsNonceT,
      keccakA, Stmt.HoldsList, Stmt.Holds]
    exact ⟨⟨by rw [e528]; exact hn, hp⟩, hk, HG⟩
  · have g1 : ∀ st ∈ fsNonceT (.n (valf% «keccak_layer» "cursor@1")) 47 544, GoodS rd S w σ st := fun st h ↦
      hg st (by simp [sqT, h])
    have gp : ∀ st ∈ padRunT 547, GoodS rd S w σ st := fun st h ↦
      hg st (by simp [sqT, h])
    have gk1 : Good rd S w σ (.keccak (sqIns 1) ((List.range 13).map fun k ↦ .n (531 + k))
        false false) := hg (.atom (.keccak (sqIns 1) ((List.range 13).map fun k ↦ .n (531 + k))
        false false)) (by simp [sqT, keccakA])
    have gk2 : Good rd S w σ (.keccak (permIns 1 [.n 545, .n 546] 548 (cap5 539))
        ((List.range 13).map fun k ↦ .n (552 + k)) false false) :=
      hg (.atom (.keccak (permIns 1 [.n 545, .n 546] 548 (cap5 539))
        ((List.range 13).map fun k ↦ .n (552 + k)) false false)) (by simp [sqT, keccakA])
    have e543 : σ (.n 544) = n := load_val (w := w) (g1 _ (List.mem_cons_self ..)) (hS7 _ _) hn
    have hp : FsPackOk σ (.n 544) (544 + 1) dsPowNonce :=
      fsPack_vals_of_good fun st h ↦ g1 st (List.mem_cons_of_mem _ h)
    have hpad : PadRunOk σ 547 := by
      simp only [padRunT, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true, GoodS, Good] at gp
      obtain ⟨z0, z1, z2, z3, z4⟩ := gp
      exact ⟨z0, by rw [z1, word_zero], by rw [z2, word_zero], by rw [z3, word_zero],
        by rw [z4, word_zero]⟩
    have hk1 := keccakA_complete gk1
    have hk2 := keccakA_complete gk2
    have hlen := pendOk_length hs.2
    obtain ⟨-, hout1⟩ := spOk_perm hs hk1 (zs := []) (by decide) rfl (by decide)
    have hcap1 := capOf_outs hout1
    have hfull : s.pend.length = rateScalars := by rw [hlen]; decide
    have hs' : SpOk σ (s.absorb (σ (.n 544)) dsPowNonce) (cap5 539, [(.n 545, .n 546)]) := by
      simp only [Fs.absorb, hfull, ↓reduceIte]
      exact ⟨hcap1, fsPackT_cells hp, trivial⟩
    obtain ⟨z0, z1, z2, z3, z4⟩ := hpad
    obtain ⟨-, hout⟩ := spOk_perm hs' hk2 (zs := [.n 548, .n 548, .n 548, .n 549, .n 550, .n 551])
      (by decide) (by simp [z1, z2, z3, z4]) (by decide)
    rw [e543] at hout
    have hpow := grind_cell (s := s) (b := 552) hout hok
    obtain ⟨-, hsq⟩ := grind_sq (s := s) (n := n) (b := 552) hout hpow
    have h553 : σ (.n (val% «keccak_layer__L1» "nxt[1]@13")) = cellsOfState (s.nonceState n) false ⟨1, by omega⟩ := grind_out1 hout
    refine ⟨e543, grind_out1 hout, hsq, fun {next kret} hnx ↦ ?_⟩
    have hgi : ∀ st ∈ gcInlineT 3 (val% «keccak_layer__L1» "wins[0]") (.n (val% «keccak_layer__L1» "nxt[1]@13")) (.n (valf% «keccak_layer» "tabs")), GoodS rd S w σ st :=
      fun st h ↦ hg st (by
        simp only [sqT, ↓reduceIte]
        exact List.mem_append_right _ h)
    have HG : Stmt.HoldsList C rd σ (gcInlineT 3 (val% «keccak_layer__L1» "wins[0]") (.n (val% «keccak_layer__L1» "nxt[1]@13")) (.n (valf% «keccak_layer» "tabs"))) next kret :=
      gcInline_holds_of_good (by decide) (by decide) (by decide) hgi hSg hrc ht
        (fun j hj ↦ by rw [h553]; exact hwin j hj) hpow hnx
    simp only [sqT, ↓reduceIte, holdsList_append, holds_fsNonceT, holds_padRunT,
      keccakA, Stmt.HoldsList, Stmt.Holds]
    exact ⟨hk1, ⟨by rw [e543]; exact hn, hp⟩, ⟨z0, z1, z2, z3, z4⟩, hk2, HG⟩

/-- **The product and `s`, completely.** -/
theorem layerA_complete {first : ℕ} (hf : first < 2) (hσ : ∀ v, σ v = σ (.n v.idx))
    (hg : ∀ s ∈ secA1 first ++ secA2 first, GoodS rd S w σ s)
    (hS7 : ∀ d off, Atom.load d (.n (valf% «keccak_layer» "cursor@1")) off ∉ S) (hS11 : ∀ d off, Atom.load d (.n (valf% «keccak_layer» "claim")) off ∉ S)
    {w0 : E} (hw : first = 1 → (σ (.n (valf% «keccak_layer» "p0")), σ (.n (valf% «keccak_layer» "p1"))) = Keccak.scalarCells w0 dsObserve)
    {c : KeccakClaim} (hmuL : c.mu.length = 16) (hval : LoadHolds rd (σ (.n (valf% «keccak_layer» "claim"))) 0 c.value)
    (hkap : LoadHolds rd (σ (.n (valf% «keccak_layer» "claim"))) 1 (sumE c.mu))
    (hmus : ∀ i < 16, LoadHolds rd (σ (.n (valf% «keccak_layer» "claim"))) (6 + i) (c.mu.getD i 0))
    {prod : List E} (hpl : prod.length = 47) (hprod : ReadsAt rd (σ (.n (valf% «keccak_layer» "cursor@1"))) prod)
    (hproj : projectedOf c prod + σ (.n (valf% «keccak_layer» "iota")) * sumE c.mu = c.value)
    {n : E} (hn : LoadHolds rd (σ (.n (valf% «keccak_layer» "cursor@1"))) 47 n)
    (hok : ((plainStart first [σ (.n (valf% «keccak_layer» "fs0")), σ (.n (valf% «keccak_layer» "fs1")), σ (.n (valf% «keccak_layer» "fs2")), σ (.n (valf% «keccak_layer» "fs3")), σ (.n (valf% «keccak_layer» "fs4"))] w0).absorbAll
      prod dsObserve).GrindOk sGrindBits n)
    (hrc : ∀ v ≤ 11, ∀ e < 2 ^ v, ∃ y t1 t2 : E, LoadHolds rd (gen ^ e) 0 t1 ∧
      wBound v = gen ^ e * y ∧ LoadHolds rd y 0 t2)
    (ht : WinTabs rd (σ (.n (valf% «keccak_layer» "tabs"))))
    (hSg : ∀ a ∈ S, loadInto (layOff first + 544) (layOff first + 544 + (gcLen 3 - 2)) a = false)
    (hwin : ∀ j ≤ gcW 3, w (layOff first + 544 + j) =
      gcWin 3 (cellsOfState (((plainStart first [σ (.n (valf% «keccak_layer» "fs0")), σ (.n (valf% «keccak_layer» "fs1")), σ (.n (valf% «keccak_layer» "fs2")), σ (.n (valf% «keccak_layer» "fs3")), σ (.n (valf% «keccak_layer» "fs4"))] w0).absorbAll
        prod dsObserve).nonceState n) false ⟨1, by omega⟩) j) :
    σ (.n (nonceV first)) = n ∧ (prodTab first).map (fun p ↦ σ (.n p.a)) = prod ∧
      σ (.n (layOff first + 532)) = cellsOfState (((plainStart first
        [σ (.n (valf% «keccak_layer» "fs0")), σ (.n (valf% «keccak_layer» "fs1")), σ (.n (valf% «keccak_layer» "fs2")), σ (.n (valf% «keccak_layer» "fs3")), σ (.n (valf% «keccak_layer» "fs4"))] w0).absorbAll prod dsObserve).nonceState
          n) false ⟨1, by omega⟩ ∧
      layerSq (plainStart first [σ (.n (valf% «keccak_layer» "fs0")), σ (.n (valf% «keccak_layer» "fs1")), σ (.n (valf% «keccak_layer» "fs2")), σ (.n (valf% «keccak_layer» "fs3")), σ (.n (valf% «keccak_layer» "fs4"))] w0) prod n =
        (σ (.n (layOff first + 531)), ⟨(cap5 (layOff first + 539)).map σ, []⟩) ∧
      ∀ {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList C rd σ (secA1 first ++ secA2 first) next kret := by
  obtain ⟨hall1, hallC⟩ := secA_atoms hf
  have hr1 := secA_resid1 hf
  have hrC := secA_residC hf
  obtain ⟨hl, hch0, hacc, hlast, hallP⟩ := prodTab_facts first hf
  have hg1 : ∀ s ∈ secA1 first, GoodS rd S w σ s := fun s hs ↦ hg s (List.mem_append_left _ hs)
  have hg2 : ∀ s ∈ secA2 first, GoodS rd S w σ s := fun s hs ↦ hg s (List.mem_append_right _ hs)
  have hgC : ∀ s ∈ checkT (accL first), GoodS rd S w σ s :=
    fun s hs ↦ hg2 s (List.mem_append_left _ hs)
  have hgS : ∀ s ∈ sqT first, GoodS rd S w σ s := fun s hs ↦ hg2 s (List.mem_append_right _ hs)
  -- the head and the product
  have H1 : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (secA1 first) next kret := by
    refine block_holds hall1 hσ hg1 ?_
    rw [hr1]
    intro a ha
    right
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      exact side_load (hS11 _ _) (hmus i (List.mem_range.mp hi))
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
      exact side_load (hS7 _ _) (hprod k (by rw [hpl]; exact List.mem_range.mp hk))
  -- the projection's value and the sponge after the product
  have hP := H1 (kret := fun _ ↦ True) trivial
  rw [secA1, holdsList_append] at hP
  obtain ⟨hcp, hmu, hR, hP⟩ := headT_holds hP
  have hs0 : SpOk σ (plainStart first [σ (.n (valf% «keccak_layer» "fs0")), σ (.n (valf% «keccak_layer» "fs1")), σ (.n (valf% «keccak_layer» "fs2")), σ (.n (valf% «keccak_layer» "fs3")), σ (.n (valf% «keccak_layer» "fs4"))] w0)
      (cap5 16, pend0 first) := by
    refine ⟨?_, ?_⟩
    · simp only [plainStart, cap5, List.map_cons, List.map_nil]
      rw [hcp 0 (by omega), hcp 1 (by omega), hcp 2 (by omega), hcp 3 (by omega),
        hcp 4 (by omega)]
    · interval_cases first
      · simp [plainStart, pend0, PendOk]
      · simp only [plainStart, pend0, ↓reduceIte, PendOk, and_true]
        rw [hcp 5 (by omega), hcp 6 (by omega)]
        exact hw rfl
  obtain ⟨hrd, hsp, hacc', -⟩ := prodT_sound hch0 hacc hallP hs0 hP
  have hprodE := prodTab_a_eq hf hpl hprod hrd
  rw [hprodE] at hsp
  have hμ : ∀ i < 16, σ (.n (muB first + i)) = c.mu.getD i 0 :=
    fun i hi ↦ loadHolds_unique (hmu i hi) (hmus i hi)
  have hp := proj_eq (muB := muB first) hl hmuL hμ
  rw [hlast, hl] at hacc'
  have hacc'' : ov σ (some (accL first)) = ((List.range 47).map fun j ↦
      ((projIdx j).map fun i ↦ σ (.n (muB first + i))).sum *
        σ (.n ((prodTab first).getD j default).a)).sum := by
    rw [hacc']
    refine congrArg List.sum (List.map_congr_left fun j hj ↦ ?_)
    rw [reader_proj hR (List.mem_range.1 hj)]
  rw [hl, ← hacc'', hprodE] at hp
  simp only [ov] at hp
  -- the check
  have HC : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (checkT (accL first)) next kret := by
    refine block_holds hallC hσ hgC ?_
    rw [hrC]
    have gc := hgC
    simp only [checkT, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, GoodS] at gc
    obtain ⟨g1, g2, g3, g4, -⟩ := gc
    have e1 := load_val g1 (hS11 _ _) hkap
    have e4 := load_val g4 (hS11 _ _) hval
    simp only [Good, V.n] at g2 g3
    have h13 : 13 < accL first := by unfold accL; split <;> norm_num
    rw [ite_pos' (by simp; omega)] at g2
    simp only [residC, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true]
    refine ⟨Or.inr (side_load (hS11 _ _) hkap), Or.inr (side_load (hS11 _ _) hval), Or.inl ?_⟩
    show σ (.n (accL first + 3)) + σ (.n (accL first + 4)) = 0
    rw [g3, g2, e1, e4, ← hproj, hp]
    exact e_add_self _
  -- the grind and the squeeze
  obtain ⟨en, h532, hsq, HS⟩ := sqT_complete (C := C) hf hsp hgS hS7 hn hok hrc ht hSg hwin
  refine ⟨en, hprodE, h532, hsq, fun {next kret} hnx ↦ ?_⟩
  rw [secA2, ← List.append_assoc, holdsList_append, holdsList_append]
  exact H1 (HC (HS hnx))

end
end LeanVM.Guest.B1.VerifySub
