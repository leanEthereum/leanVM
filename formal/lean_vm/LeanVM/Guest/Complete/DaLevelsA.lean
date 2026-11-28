module

public import LeanVM.Guest.Complete.LoopFA
public import LeanVM.Guest.Complete.DaPadA
public import LeanVM.Guest.Complete.MainFree
import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_levels__L»

/-!
# `da_levels`, placed

`da_levels(tree)` over `2^k` leaves at index `b` (`TreeMem`) reads and writes only the tree's
cells (`treeR b k`) and places nothing of its own. Each level loop completes placed by
`loopF_callAtA`, its block's valuation `lvl_block`'s, its loads through the level's two pointers
(`ptr_sound`) inside the tree (`lvlLoop_callAtA`); the node's valuation is one memory's
evaluation, which holds on every memory with the tree, its only memory atoms the root's two
loads (`dl_callAtA`). `kidsAtF_taken`: callees all entered, each completing at every position.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Da LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier
open LeanVM.Guest.Value
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- The cells of the tree over `2^k` leaves at index `b`. -/
def treeR (b k i : ℕ) : Prop := b ≤ i ∧ i < b + 4 * 2 ^ k

/-! ## Callees all entered -/

/-- **Callees all entered, each completing at every position**, chain from every cursor. -/
theorem kidsAtF_taken {k : ℕ} {σ : Val} {R : ℕ → Prop} {Pre Oend : Reader → Prop} {D : ℕ} :
    ∀ (cs : List Call) (O : Reader → Prop) (Dacc : ℕ → Prop) (cur : ℕ), (∀ rd, O rd → Oend rd) →
    (∀ c ∈ cs, c.taken = true ∧ ∀ cur', ∃ Bc ec, ec ≤ cur' + D ∧
      CallAtA fs al cert k c.f (c.args.map σ) (c.rets.map σ) R
      (fun _ => False) (fun _ => True) Pre (fun _ _ => True) Bc (allocBase (al c.f) cur')
      (allocBase (al c.f) cur' + Bc) ec) →
    ∃ e, e ≤ cur + cs.length * D ∧ KidsAtF fs al cert k σ R Pre O Dacc [] cs cur e Oend (fun _ => False)
  | [], O, Dacc, cur, hO, _ => ⟨cur, by simp, by rw [KidsAtF]; exact ⟨rfl, hO, fun _ h => h.elim⟩⟩
  | c :: cs, O, Dacc, cur, hO, h => by
    obtain ⟨ht, hc⟩ := h c List.mem_cons_self
    obtain ⟨Bc, ec, hb, hca⟩ := hc cur
    obtain ⟨e, heb, he⟩ := kidsAtF_taken cs (fun rd => O rd ∧ True) (fun i => Dacc i ∨ False) ec
      (fun rd h => hO rd h.1) fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    refine ⟨e, ?_, ?_⟩
    · rw [List.length_cons, Nat.succ_mul]; omega
    rw [KidsAtF]
    simp only [ht, ↓reduceIte]
    exact ⟨Bc, ec, R, fun _ => False, fun _ => True, fun i hi => Or.inl hi,
      hca.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun _ h => h.1) (fun _ _ _ h => h), he⟩

/-! ## A level loop -/

theorem holds_of_pure {rd rd' : Reader} {σ : Val} {a : Atom} (hn : needsSide a = false)
    (h : a.Holds rd σ) : a.Holds rd' σ := by
  cases a <;> simp_all [needsSide, Atom.Holds]

set_option maxRecDepth 10000 in
/-- **A level loop completes placed** from its first counter, reading and writing the tree. -/
theorem lvlLoop_callAtA {K k lvl : ℕ} (hl : lvl < k) (hk : k ≤ 10) {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) (hlp : coreProgram.loop f = true)
    (hpl : (loopPre fn).all loopPlainB = true)
    (hok : lvlOk fn f (off k lvl) (off k (lvl + 1)) = true)
    (hcok : lvlCOk fn (off k lvl) (off k (lvl + 1)) = true)
    {b : ℕ} {leaves : List (E × E)} (hlen : leaves.length = 2 ^ k) {Pre : Reader → Prop}
    (hmem : ∀ rd, LowDef K rd → Pre rd → TreeMem rd (ptrAt b) k leaves) (fp c : ℕ)
    (hfc : fp + lpBlk fs f (2 ^ (k - lvl - 1)) ≤ c) :
    CallAtA fs al cert K f [1, gen ^ 2 ^ (k - lvl - 1), ptrAt b] [] (treeR b k) (fun _ => False)
      (fun _ => True) Pre (fun _ _ => True) (lpBlk fs f (2 ^ (k - lvl - 1))) fp c c := by
  simp only [lvlOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨hshape, hplen⟩, hld⟩, -⟩, -⟩, -⟩ := hok
  simp only [lvlCOk, Bool.and_eq_true, Option.isSome_iff_exists, decide_eq_true_eq] at hcok
  obtain ⟨⟨⟨⟨⟨⟨⟨c2, hchk2⟩, hatoms⟩, hneeds2⟩, hS2⟩, hpa⟩, hpb⟩, hsp⟩ := hcok
  have hpar : fn.params = [.n 0, .n 1, .n 2] := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hplen]; rfl
  have h2 : 2 ^ (k - lvl) = 2 * 2 ^ (k - lvl - 1) := by rw [← pow_succ']; congr 1; omega
  have hkl : 2 ^ (k - lvl) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hk1 : 1 ≤ 2 ^ (k - lvl - 1) := Nat.one_le_two_pow
  have hm : 2 ^ (k - lvl - 1) < 2 ^ 34 := by
    have : 2 ^ (k - lvl - 1) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h := loopF_callAtA (fs := fs) (al := al) (cert := cert) (k := K) hf hshape hlp hpl hm
    (rest := [ptrAt b]) (R := treeR b k) (Pre := Pre) ?_ 0 (by omega) fp c (by simpa using hfc)
  · simpa using h
  intro j hj rd hl' hp
  obtain ⟨σ, hpσ, hs⟩ := lvl_block hl hk (by split <;> decide) hshape hplen hld hatoms hchk2 hneeds2 hS2 hpa
    hpb hsp hlen (hmem rd hl' hp) hj
  have hat := atoms_of_flat hs
  rw [hpar] at hpσ
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpσ
  obtain ⟨e0, e1, e2⟩ := hpσ
  have hsub : 2 ^ (k - (lvl + 1)) = 2 ^ (k - lvl - 1) := by rw [Nat.sub_add_eq]
  have hpure : ∀ a ∈ (atomsIn (loopPre fn)).filter pureB, a.Holds rd σ := fun a ha =>
    hat a (List.mem_filter.mp ha).1
  have hσa := ptr_sound hpa hpure (off_lt hk)
  have hσb := ptr_sound hpb hpure (off_lt hk)
  rw [e0, e2, ← pow_mul, ptrAt_mul_gen_pow, ptrAt_mul_gen_pow] at hσa hσb
  refine ⟨σ, by rw [hpar]; simp [e0, e1, e2], fun s hsm => ?_, fun q hq => ?_⟩
  · have := List.all_eq_true.mp hatoms s hsm
    cases s <;> simp only [Bool.false_eq_true] at this
    exact (hs _ hsm).1
  · obtain ⟨s, hsm, hsq⟩ := List.mem_filterMap.mp hq
    cases s with
    | atom a =>
      cases a with
      | load d p o =>
        simp only [stmtLoad?, Option.some.injEq] at hsq
        subst hsq
        have hn := List.all_eq_true.mp hneeds2 _ (mem_atomsIn hsm)
        simp only [needsSide, Bool.not_true, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at hn
        rcases hn with hn | hn
        · rw [hS2] at hn
          simp only [List.mem_cons, Atom.load.injEq, List.not_mem_nil, or_false] at hn
          rcases hn with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
          · refine ⟨_, by rw [hσb]; exact Main.addr_ofK _ _, ?_⟩
            unfold treeR off; omega
          · refine ⟨_, by rw [hσb]; exact Main.addr_ofK _ _, ?_⟩
            unfold treeR off; omega
        · simp only [isLoadVia, Bool.and_eq_true, decide_eq_true_eq] at hn
          obtain ⟨⟨rfl, -⟩, ho⟩ := hn
          refine ⟨_, by rw [hσa]; exact Main.addr_ofK _ _, ?_⟩
          unfold treeR off; omega
      | _ => simp [stmtLoad?] at hsq
    | _ => simp [stmtLoad?] at hsq

/-! ## A specialization -/

/-- Entry `k`'s body places nothing and is no loop helper; its level loops are loop helpers whose
blocks are atoms placing nothing. -/
noncomputable def dlPlainOk (k : ℕ) : Bool :=
  let e := dlEntry k
  (coreProgram.getD e.2.2.1 default).body.all plainS && !coreProgram.loop e.2.1 &&
  (List.range k).all fun lvl =>
    match coreIdx? (e.2.2.2.getD lvl "") (dlLoopAt k lvl) with
    | some j => coreProgram.loop (e.2.2.2.getD lvl "") && (loopPre (coreProgram.getD j default)).all loopPlainB
    | none => true

/-- `da_levels`' callees, at most one per level. -/
noncomputable def dlCallsOk (k : ℕ) : Bool :=
  match splitRet (coreProgram.getD (dlEntry k).2.2.1 default).body with
  | some (P, _) => decide ((P.filterMap Stmt.callS).length ≤ k)
  | none => false

set_option maxRecDepth 100000 in
theorem dlCalls_ok5 : dlCallsOk 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem dlCalls_ok7 : dlCallsOk 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem dlPlain_ok5 : dlPlainOk 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem dlPlain_ok7 : dlPlainOk 7 = true := by decide +kernel

theorem one_add_gen_pow_ne' {Q : ℕ} (h1 : 1 ≤ Q) (h2 : Q < 2 ^ 30) : (1 : E) + gen ^ Q ≠ 0 := by
  intro h0
  have : gen ^ Q = gen ^ 0 := by rw [pow_zero]; exact (CharTwo.add_eq_zero.mp h0).symm
  exact absurd (gen_pow_inj (by omega) (by omega) this) (by omega)

set_option maxRecDepth 100000 in
/-- **A checked specialization completes placed**, reading and writing its tree only. -/
theorem dl_callAtA' (hfs : ∀ g, fs g < 2 ^ 16) {K k : ℕ} (hk : k ≤ 10) (hok : dlEntryOk k = true)
    (hcok : dlCEntryOk k = true) (hpok : dlPlainOk k = true) (hcls : dlCallsOk k = true) {b : ℕ}
    {leaves : List (E × E)} (hlen : leaves.length = 2 ^ k)
    {Pre : Reader → Prop} (hmem : ∀ rd, LowDef K rd → Pre rd → TreeMem rd (ptrAt b) k leaves) {fp c : ℕ}
    (hfc : fp + fs (daLevelsName k) ≤ c) :
    ∃ e, e ≤ c + 2 ^ 30 ∧ CallAtA fs al cert K (daLevelsName k) [ptrAt b] [(cellRoot k leaves).1, (cellRoot k leaves).2]
      (treeR b k) (fun _ => False) (fun _ => True) Pre (fun _ _ => True) (fs (daLevelsName k)) fp c e := by
  by_cases hex : ∃ rd0, LowDef K rd0 ∧ Pre rd0
  swap
  · exact ⟨c, by omega, [], ⟨by simp, List.Pairwise.nil⟩, le_rfl, fun _ _ => trivial,
      fun rd hl _ hp => absurd ⟨rd, hl, hp⟩ hex⟩
  unfold dlCallsOk at hcls
  obtain ⟨rd0, hl0, hp0⟩ := hex
  have hmem0 := hmem rd0 hl0 hp0
  unfold dlEntryOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨-, hname⟩, hidx⟩, hlt⟩, hdl⟩, hloops⟩ := hok
  replace hidx := coreIdx?_eq hidx
  unfold dlCEntryOk at hcok
  simp only [Bool.and_eq_true, Option.isSome_iff_exists, List.isEmpty_iff, List.all_eq_true,
    List.mem_range] at hcok
  obtain ⟨⟨⟨⟨c', hchk⟩, hst⟩, hbody⟩, hcloops⟩ := hcok
  unfold dlPlainOk at hpok
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range] at hpok
  obtain ⟨⟨hplB, hnl⟩, hplL⟩ := hpok
  set e := dlEntry k
  set fn := coreProgram.getD e.2.2.1 default
  have hf := find_of_idx hidx hlt
  rw [← hname] at hfc ⊢
  unfold dlOk at hdl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hdl
  obtain ⟨⟨hparams, -⟩, hdl⟩ := hdl
  split at hdl
  case h_2 => exact absurd hdl (by simp)
  rename_i P vs hsr
  rw [hsr] at hbody
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at hdl hbody
  obtain ⟨⟨⟨⟨rfl, -⟩, hguards⟩, hr0⟩, hr1⟩ := hdl
  obtain ⟨hneeds, hcalls⟩ := hbody
  rw [hsr] at hcls
  have hncl : (P.filterMap Stmt.callS).length ≤ k := of_decide_eq_true hcls
  have hb := splitRet_eq hsr
  let σ : Val := B1.Val.ofArgs (ev rd0 (fun _ => 0) [ptrAt b] fn.body)
  obtain ⟨-, -, hgs⟩ := ev_spec rd0 (fun _ => 0) fn.body [ptrAt b] hchk
  rw [show [ptrAt b].length = 1 from rfl, hst] at hgs
  have hg : ∀ a ∈ atomsIn P, Good rd0 [] (fun _ => 0) σ a := fun a ha =>
    hgs (.atom a) (by rw [hb]; exact List.mem_append_left _ (atom_mem_of_atomsIn ha))
  have e0 : σ (.n (valf% «da_levels» "tree")) = ptrAt b := ev_params rd0 _ (l := [ptrAt b]) hchk (by simp)
  have h2k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  -- the root's cells, on every memory with the tree
  have hroot : ∀ rd, TreeMem rd (ptrAt b) k leaves → ∀ i < 2, LoadHolds rd (ptrAt b) (4 * 2 ^ k - 4 + i)
      ((pairCells (treeLvl leaves k)).getD i 0) := by
    intro rd hm i hi
    have := treeMem_load hlen hm (l := k) le_rfl (i := i) (by simp; omega)
    rwa [off_self, loadHolds_mul_gen_pow] at this
  have hval : ∀ (x : V) (o i : ℕ), i < 2 → o = 4 * 2 ^ k - 4 + i →
      (atomsIn P).any (isLoadAt x (.n (valf% «da_levels» "tree")) o) = true →
      σ x = (pairCells (treeLvl leaves k)).getD i 0 := by
    intro x o i hi ho hx
    rw [good_load_of_any rfl hg hx, e0, ho, rdAt_of_load (hroot rd0 hmem0 i hi)]
  have v0 := hval _ _ 0 (by omega) rfl hr0
  have v1 := hval _ _ 1 (by omega) (by omega) hr1
  -- the memory atoms are the root's loads
  have hside : ∀ a ∈ atomsIn P, needsSide a = true →
      (∃ x, a = .load x (.n (valf% «da_levels» "tree")) (4 * 2 ^ k - 4) ∧ σ x = (pairCells (treeLvl leaves k)).getD 0 0) ∨
      (∃ x, a = .load x (.n (valf% «da_levels» "tree")) (4 * 2 ^ k - 4 + 1) ∧
        σ x = (pairCells (treeLvl leaves k)).getD 1 0) := by
    intro a ha hns
    rcases hneeds a ha with (h | h) | h
    · rw [hns] at h; exact absurd h (by simp)
    all_goals
      cases a <;> simp only [isLoadAt, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    · exact Or.inl ⟨_, rfl, v0⟩
    · exact Or.inr ⟨_, by rw [show 4 * 2 ^ k - 3 = 4 * 2 ^ k - 4 + 1 by omega], v1⟩
  have hat0 : ∀ a ∈ atomsIn P, a.Holds rd0 σ := by
    refine atoms_holds hg fun a ha hns => Or.inl ?_
    rcases hside a ha hns with ⟨x, rfl, hx⟩ | ⟨x, rfl, hx⟩
    · show LoadHolds rd0 (σ _) _ (σ x); rw [hx, e0]; exact hroot rd0 hmem0 0 (by omega)
    · show LoadHolds rd0 (σ _) _ (σ x); rw [hx, e0]; exact hroot rd0 hmem0 1 (by omega)
  have hat : ∀ rd, TreeMem rd (ptrAt b) k leaves → ∀ a ∈ atomsIn P, a.Holds rd σ := by
    intro rd hm a ha
    cases hns : needsSide a
    · exact holds_of_pure hns (hat0 a ha)
    · rcases hside a ha hns with ⟨x, rfl, hx⟩ | ⟨x, rfl, hx⟩
      · show LoadHolds rd (σ _) _ (σ x); rw [hx, e0]; exact hroot rd hm 0 (by omega)
      · show LoadHolds rd (σ _) _ (σ x); rw [hx, e0]; exact hroot rd hm 1 (by omega)
  -- the guarded loops
  have hlvl : ∀ lvl < k, σ (.n (5 * lvl + 3)) = 1 + gen ^ 2 ^ (k - lvl - 1) ∧ σ (.n (5 * lvl + 4)) = 1 ∧
      σ (.n (5 * lvl + 5)) = gen ^ 2 ^ (k - lvl - 1) := by
    intro lvl hl
    have hg' := hguards lvl hl
    simp only [guardPowOk, Bool.and_eq_true] at hg'
    obtain ⟨⟨⟨-, ha⟩, h1⟩, hN⟩ := hg'
    have hm : 2 ^ (k - lvl - 1) < 2 ^ 64 := by
      have : 2 ^ (k - lvl - 1) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    split at ha
    case h_2 => exact absurd ha (by simp)
    rename_i pp qq hpq
    simp only [Bool.and_eq_true] at ha
    exact ⟨by rw [addOf_sound hpq (hat0), const_sound ha.1 hat0, word_one, constPow_sound ha.2 hat0 hm],
      by rw [const_sound h1 hat0, word_one], constPow_sound hN hat0 hm⟩
  have hsP : P.all Stmt.straight = true := List.all_eq_true.mpr fun s hs => by
    have := hcalls s hs
    cases s <;> first | rfl | simp at this
  have hpP : P.all plainS = true := List.all_eq_true.mpr fun s hs =>
    hplB s (by rw [hb]; exact List.mem_append_left _ hs)
  -- the callees
  have hkid : ∀ cc ∈ (P.filterMap Stmt.callS).map (mkCall σ), cc.taken = true ∧ ∀ cur', ∃ Bc ec,
      ec ≤ cur' + 2 ^ 26 ∧ CallAtA fs al cert K cc.f (cc.args.map σ) (cc.rets.map σ) (treeR b k) (fun _ => False) (fun _ => True)
        Pre (fun _ _ => True) Bc (allocBase (al cc.f) cur') (allocBase (al cc.f) cur' + Bc) ec := by
    intro cc hcc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hcc
    obtain ⟨s, hs, hsx⟩ := List.mem_filterMap.mp hx
    have := hcalls s hs
    cases s with
    | callIf gc g args =>
      simp only at this
      obtain ⟨lvl, hl, heq⟩ := List.any_eq_true.mp this
      have hl' := List.mem_range.mp hl
      have hs' := stmtEqb_sound heq
      simp only [lvlCall, Stmt.callIf.injEq] at hs'
      obtain ⟨rfl, rfl, rfl⟩ := hs'
      simp only [Stmt.callS, Option.some.injEq] at hsx
      subst hsx
      obtain ⟨hgc, hone, hNv⟩ := hlvl lvl hl'
      have hm30 : 2 ^ (k - lvl - 1) < 2 ^ 30 := by
        have : 2 ^ (k - lvl - 1) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      refine ⟨decide_eq_true (by
          show σ (.n (5 * lvl + 3)) ≠ 0
          rw [hgc]; exact one_add_gen_pow_ne' Nat.one_le_two_pow hm30), fun cur' => ?_⟩
      have hlo := hloops lvl hl'
      have hclo := hcloops lvl hl'
      have hpl' := hplL lvl hl'
      unfold loopOk at hlo
      unfold loopCOk at hclo
      split at hlo
      case h_2 => exact absurd hlo (by simp)
      rename_i j hj
      rw [hj] at hclo hpl'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hlo hpl'
      obtain ⟨hjl, hlok⟩ := hlo
      have hfl := find_of_idx (coreIdx?_eq hj) hjl
      refine ⟨lpBlk fs (e.2.2.2.getD lvl "") (2 ^ (k - lvl - 1)),
        allocBase (al (e.2.2.2.getD lvl "")) cur' + lpBlk fs (e.2.2.2.getD lvl "") (2 ^ (k - lvl - 1)), ?_, ?_⟩
      · have h1 := allocBase_le (al (e.2.2.2.getD lvl "")) cur'
        have h2 : 2 ^ (k - lvl - 1) * fs (e.2.2.2.getD lvl "") ≤ 2 ^ 9 * 2 ^ 16 :=
          Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega)) (hfs _).le
        have h3 := hfs (tailKey (e.2.2.2.getD lvl ""))
        unfold lpBlk
        omega
      have := lvlLoop_callAtA (fs := fs) (al := al) (cert := cert) (K := K) hl' hk hfl hpl'.1 hpl'.2 hlok hclo
        hlen hmem (allocBase (al (e.2.2.2.getD lvl "")) cur')
        (allocBase (al (e.2.2.2.getD lvl "")) cur' + lpBlk fs (e.2.2.2.getD lvl "") (2 ^ (k - lvl - 1))) le_rfl
      show CallAtA fs al cert K _ [σ (.n (5 * lvl + 4)), σ (.n (5 * lvl + 5)), σ (.n (valf% «da_levels» "tree"))] [] _ _ _ _ _ _ _ _ _
      rw [hone, hNv, e0]
      exact this
    | atom a => simp [Stmt.callS] at hsx
    | _ => simp at this
  obtain ⟨eK, hKb, hK⟩ := kidsAtF_taken (fs := fs) (al := al) (cert := cert) (k := K) (σ := σ) (R := treeR b k)
    (Pre := Pre) (Oend := fun rd => HoldsWords rd []) _ (fun rd => HoldsWords rd []) (fun _ => False) c
    (fun _ h => h) hkid
  refine ⟨eK, ?_, callAtA_straight hf hb hsP hpP hnl hfc σ (by rw [hparams]; simp [e0]) ?_ ?_ [] _ _ hK
    (fun _ _ => trivial) ?_ (fun _ _ _ _ _ _ _ => trivial)⟩
  · rw [List.length_map] at hKb
    have : (P.filterMap Stmt.callS).length * 2 ^ 26 ≤ 10 * 2 ^ 26 := Nat.mul_le_mul_right _ (by omega)
    omega
  · show [σ (.n (5 * k + 1)), σ (.n (5 * k + 2))] = _
    rw [v0, v1, cellRoot_treeLvl, List.headD_eq_getD]
    obtain ⟨q0, q1⟩ := pairCells_getD' (treeLvl leaves k) 0
    simp only [Nat.mul_zero, Nat.zero_add] at q0 q1
    rw [q0, q1]
  · intro q hq
    obtain ⟨s, hs, hsq⟩ := List.mem_filterMap.mp hq
    cases s with
    | atom a =>
      cases a with
      | load d p o =>
        simp only [stmtLoad?, Option.some.injEq] at hsq
        subst hsq
        rcases hside _ (mem_atomsIn hs) rfl with ⟨x, hx, -⟩ | ⟨x, hx, -⟩ <;>
          simp only [Atom.load.injEq] at hx <;> obtain ⟨-, rfl, rfl⟩ := hx <;>
          refine ⟨_, by rw [e0]; exact Main.addr_ofK _ _, ?_⟩ <;> unfold treeR <;> omega
      | _ => simp [stmtLoad?] at hsq
    | _ => simp [stmtLoad?] at hsq
  · intro rd hl hp _ s hs
    have hm := hmem rd hl hp
    have := hcalls s hs
    cases s with
    | atom a => exact hat rd hm a (mem_atomsIn hs)
    | callIf gc g args =>
      simp only at this
      obtain ⟨lvl, hl', heq⟩ := List.any_eq_true.mp this
      have hs' := stmtEqb_sound heq
      simp only [lvlCall, Stmt.callIf.injEq] at hs'
      obtain ⟨rfl, -, -⟩ := hs'
      show IsInK (σ (.n (5 * lvl + 3)))
      rw [(hlvl lvl (List.mem_range.mp hl')).1, ← pow_zero gen]
      exact gen_pow_add_isInK _ _
    | _ => simp at this

/-- **`da_levels` completes placed** at both depths, reading and writing its tree only. -/
theorem dl_callAtA (hfs : ∀ g, fs g < 2 ^ 16) {K k : ℕ} (hd : DlDepth k) {b : ℕ} {leaves : List (E × E)}
    (hlen : leaves.length = 2 ^ k)
    {Pre : Reader → Prop} (hmem : ∀ rd, LowDef K rd → Pre rd → TreeMem rd (ptrAt b) k leaves) {fp c : ℕ}
    (hfc : fp + fs (daLevelsName k) ≤ c) :
    ∃ e, e ≤ c + 2 ^ 30 ∧ CallAtA fs al cert K (daLevelsName k) [ptrAt b] [(cellRoot k leaves).1, (cellRoot k leaves).2]
      (treeR b k) (fun _ => False) (fun _ => True) Pre FreePost (fs (daLevelsName k)) fp c e := by
  have h : ∃ e, e ≤ c + 2 ^ 30 ∧ CallAtA fs al cert K (daLevelsName k) [ptrAt b]
      [(cellRoot k leaves).1, (cellRoot k leaves).2]
      (treeR b k) (fun _ => False) (fun _ => True) Pre (fun _ _ => True) (fs (daLevelsName k)) fp c e := by
    rcases hd with rfl | rfl
    · exact dl_callAtA' hfs (by decide) dl_ok5 dlc_ok5 dlPlain_ok5 dlCalls_ok5 hlen hmem hfc
    · exact dl_callAtA' hfs (by decide) dl_ok7 dlc_ok7 dlPlain_ok7 dlCalls_ok7 hlen hmem hfc
  obtain ⟨e, he, h⟩ := h
  exact ⟨e, he, h.free (da_levels_free hd).1 (da_levels_free hd).2⟩

end
end LeanVM.Guest.Complete
