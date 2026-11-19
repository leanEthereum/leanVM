/-
  LeanVM.Guest.Bridge.JumpCells

  The jump cells of the deployed guest: every frame of the tree track against the reference run holds, at the cells its function's alignment check names, what its jumps read.
-/

module

public import LeanVM.Guest.Bridge.FrameMap
public import LeanVM.Guest.Bridge.StepRule
public import LeanVM.Guest.Bridge.JumpCellsPack
public import LeanVM.Guest.Bridge.JumpCellsSound
public import LeanVM.Guest.B2C.CplWalk
public import LeanVM.Guest.B2C.Table
public import LeanVM.Guest.SoundFacts
public import LeanVM.Guest.Mode.SoundOp
public import LeanVM.Guest.Mode.Step
public import LeanVM.Guest.Memory.Discharge
public import LeanVM.Guest.Bridge.ProgAlDefs
public import LeanVM.Guest.Bridge.JumpCellsIdx

/-!
# The jump cells of the deployed guest

`AShape A`: the alignment contexts of `A` are the data's (`AlignCtx.ofData` over function `j`'s certificate cells, `Plumb`, entry, whether it is `main`, the guest's powers and jump table), their hint-only cells only values without a certificate cell (below `2`), their code the compiled function's. `jcData j` (`JumpCellsIdx.lean`): `jcDataD` on function `j`'s data, which the kernel decides for every function (`Bridge/JumpCells/`). `ChainArm`: at a chained `match`'s table jump, the arm the previous selector took is one whose target cell the jump reads, what the alignment check cannot see (the chained `match` follows the previous one, its jump repeated at the end of each arm); only `main_loop2` has chains (`B2C.chained_only`).

`jumpCells_of` (`JumpCellsOf.lean`, apart: it reads the program's alignment, `progAl`): on the honest tree and a memory covering its writes, under `ProgAl`, `AShape`, every function's `jcData` and `ChainArm`, the top frame of every state of the track against the run has its jump cells (`JumpCells`), each from what its frame holds (`FrameHolds`, `RefOk.frames`): the fixed cells' constants and frame words, a condition at its certificate cell (`walk_inK`, `locAt_ofData`), a table jump's target through the jump table (`tbl_armWord`), a call site's callee frame and header (the site the check names `siteOf`'s, no two sites of one argument list; a loop helper's last call no site's, `loop_last`), a loop's tail call to the frame right after its own (`FrameHolds.tail`), its header; `main` at frame `0` (no path calls `main`, `insts_main`) and only `main` (`Memory.insts_same`).
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B2C
open LeanVM.Guest.Check (getF getF_eq)

@[expose] public section

/-- **The alignment contexts are the data's**: for function `j`, over its certificate's cells
(hint-only cells only for values without one), `Plumb`, entry, whether it is `main`, the guest's
powers and jump table; its code the compiled function's. -/
def AShape (A : String → FnAl) : Prop :=
  ∀ f j, idxOf f = some j → (A f).code = (fnOf j).code ∧ ∃ extra ents halt len,
    (A f).X = AlignCtx.ofData (certOf j).locs extra (fnOf j).entryPc (j == 1) (plumbOf j) Data.powTree
      Data.jtTrie ents halt len ∧ ∀ i c, extra.lookup i = some c → (certOf j).locs.getD i 0 < 2

/-- **The arm a chained `match`'s table jump comes from**: at a state of the track whose top frame
is at a jump reading a chained `match`'s target cell `od`, the previous selector took an arm whose
target cell is `od`. -/
def ChainArm (rd : Reader) (Is : List Inst) (T : Tree) (M : ℕ → E) (A : String → FnAl) : Prop :=
  ∀ pc fp done e st, RefOk coreProgram rd Is T M (entOf A) (alOf A) pc fp (done, e :: st) →
    ∀ j, idxOf e.I.t.name = some j → ∀ off oc od of, pc = entOf A e.I.t.name + off →
      (A e.I.t.name).code[off]? = some (.jump oc od of) → ∀ ch ∈ (plumbOf j).chains, od ∈ ch.2.2.1 →
        ∃ k, ch.2.2.1[k]? = some od ∧ e.σ (V.n ch.2.1) = ofK (addressOfIndex k)

end

public section

/-! ## The context's tables -/

section Ctx

variable {locs : List ℕ} {extra : List (ℕ × ℕ)} {entry : ℕ} {main : Bool} {p : Plumb} {pows : Exec.PowTree}
  {jt : Exec.Trie ℕ} {ents : List (String × ℕ)} {halt len : ℕ}

theorem statOf_ofData {o : ℕ} {v : PC}
    (h : (AlignCtx.ofData locs extra entry main p pows jt ents halt len).statOf o = some v) : (o, v) ∈ p.stat :=
  getF_trieOf h

theorem arms_ofData {od : ℕ} {a : ℕ × ℕ}
    (h : getF (AlignCtx.ofData locs extra entry main p pows jt ents halt len).arms od = some a) :
    (od, a) ∈ armsOf p :=
  getF_trieOf h

theorem siteAt_ofData {q : ℕ} {args rets : List V} {s : Site}
    (h : (AlignCtx.ofData locs extra entry main p pows jt ents halt len).siteAt q args rets = some s) :
    s ∈ p.sites ∧ s.q = q ∧ s.args = args.map (·.idx) ∧ s.rets = rets.map (·.idx) := by
  unfold AlignCtx.siteAt at h
  split at h
  · rename_i s' hs'
    have hm := getF_trieOf hs'
    obtain ⟨s'', hs'', he⟩ := List.mem_map.mp hm
    simp only [Prod.mk.injEq] at he
    obtain ⟨hq, rfl⟩ := he
    cases hb : (s''.args == args.map (·.idx) && s''.rets == rets.map (·.idx)) <;>
      simp only [hb, Bool.cond_true, Bool.cond_false] at h
    · cases h
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq] at hb
    exact ⟨hs'', hq, hb.1, hb.2⟩
  · cases h

end Ctx

/-! ## Sites, kids and instances -/

theorem sitesUniq_eq : ∀ {ss : List Site}, sitesUniq ss = true → ∀ {s s' : Site}, s ∈ ss → s' ∈ ss →
    s.args = s'.args → s.rets = s'.rets → s = s'
  | [], _, _, _, hs, _, _, _ => absurd hs List.not_mem_nil
  | a :: ss, h, s, s', hs, hs', ha, hr => by
    simp only [sitesUniq, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      beq_eq_false_iff_ne] at h
    obtain ⟨h1, h2⟩ := h
    rcases List.mem_cons.mp hs with e1 | m1 <;> rcases List.mem_cons.mp hs' with e2 | m2
    · rw [e1, e2]
    · subst e1
      rcases h1 s' m2 with h | h
      · exact absurd ha.symm h
      · exact absurd hr.symm h
    · subst e2
      rcases h1 s m1 with h | h
      · exact absurd ha h
      · exact absurd hr h
    · exact sitesUniq_eq h2 m1 m2 ha hr

theorem siteOf_eq {j : ℕ} {c : Call} {s : Site} (hu : sitesUniq (plumbOf j).sites = true) (hs : s ∈ (plumbOf j).sites)
    (ha : s.args = c.args.map (·.idx)) (hr : s.rets = c.rets.map (·.idx)) : siteOf j c = some s := by
  unfold siteOf
  obtain ⟨s', hs'⟩ : ∃ s', (plumbOf j).sites.find? (fun s ↦ s.args == c.args.map (·.idx) &&
      s.rets == c.rets.map (·.idx)) = some s' :=
    Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨s, hs, by simp [ha, hr]⟩)
  have hp := List.find?_some hs'
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  rw [hs', sitesUniq_eq hu (List.mem_of_find?_eq_some hs') hs (hp.1.trans ha.symm) (hp.2.trans hr.symm)]

theorem kidsValid_get {P : Core.Program} {rv : Reader} {σ : Val} : ∀ {cs : List Memory.Call} {ks : List Tree} {i : ℕ}
    {c : Memory.Call}, Tree.KidsValid P rv σ cs ks → cs[i]? = some c → ∃ k, ks[i]? = some k ∧ k.name = c.f ∧
      (c.taken = true → ∃ args rets, k.Valid P rv args rets)
  | [], _, _, _, _, hc => by simp at hc
  | _ :: _, [], _, _, h, _ => h.elim
  | c' :: cs, k :: ks, 0, c, h, hc => by
    obtain rfl := Option.some.inj hc
    have hv := h.2.1
    refine ⟨k, rfl, h.1, fun ht ↦ ⟨c'.args.map σ, c'.rets.map σ, ?_⟩⟩
    rw [ite_eq_left ht] at hv
    exact hv
  | _ :: cs, _ :: ks, i + 1, c, h, hc => by
    obtain ⟨k, hk, hn, hv⟩ := kidsValid_get (i := i) h.2.2 (by simpa using hc)
    exact ⟨k, by simpa using hk, hn, hv⟩

mutual
/-- An instance of a subtree is its root at its frame, or not named `main`. -/
theorem insts_main_or {fs : String → ℕ} {lp : String → Bool} {H : Inst → ℕ → E × E} {rv : Reader} :
    ∀ (t : Tree) (p : ℕ × ℕ) (hdr : E × E) {args rets : List E}, t.Valid coreProgram rv args rets →
      ∀ I ∈ t.insts fs lp H p hdr, (I.fp = p.1 ∧ I.t = t) ∨ I.t.name ≠ "main"
  | .node f σ bufs kids, p, hdr, args, rets, hv, I, hI => by
    rw [insts_node, List.mem_cons] at hI
    rcases hI with rfl | hI
    · exact Or.inl ⟨rfl, rfl⟩
    · obtain ⟨fn, hf, -, es, vs, hw, -, -, hk⟩ := hv
      exact Or.inr (instsKids_main kids σ (calls es) _ 0 _ hk (fun c hc ↦ calls_ne_main hf hw hc) I hI)
  | .phantom .., _, _, _, _, hv, _, _ => hv.elim

theorem instsKids_main {fs : String → ℕ} {lp : String → Bool} {H : Inst → ℕ → E × E} {rv : Reader} :
    ∀ (ks : List Tree) (σ : Val) (cs : List Memory.Call) (I : Inst) (j : ℕ) (ps : List (ℕ × ℕ)),
      Tree.KidsValid coreProgram rv σ cs ks → (∀ c ∈ cs, c.f ≠ "main") →
        ∀ J ∈ Tree.instsKids fs lp H I j ps ks, J.t.name ≠ "main"
  | [], _, _, _, _, _, _, _, J, hJ => by rw [instsKids_nil] at hJ; exact (List.not_mem_nil hJ).elim
  | _ :: _, _, _, _, _, [], _, _, J, hJ => by rw [instsKids_nil_left] at hJ; exact (List.not_mem_nil hJ).elim
  | k :: ks, σ, c :: cs, I, j, p :: ps, ⟨hn, hc, hks⟩, hm, J, hJ => by
    rw [instsKids_cons, List.mem_append] at hJ
    rcases hJ with hJ | hJ
    · have hcm := hm c List.mem_cons_self
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        rcases insts_main_or k p _ hc J hJ with ⟨-, rfl⟩ | h
        · rw [hn]; exact hcm
        · exact h
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
        rw [insts_phantom, List.mem_singleton] at hJ
        subst hJ
        simp only [Tree.name] at hn ⊢
        rw [hn]; exact hcm
    · exact instsKids_main ks σ cs I (j + 1) ps hks (fun c' hc' ↦ hm c' (List.mem_cons_of_mem _ hc')) J hJ
  | _ :: _, _, [], _, _, _ :: _, h, _, _, _ => h.elim
end

/-! ## The jump cells -/

theorem mem_of_lookupN {β : Type} : ∀ {l : List (ℕ × β)} {o : ℕ} {c : β}, l.lookup o = some c → (o, c) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | ⟨k, b⟩ :: l, o, c, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i he
      cases h
      have : o = k := by simpa using he
      rw [this]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_lookupN h)

/-- **A certificate cell read in its window** is the certificate's. -/
theorem cellW_spec {C : Check.Cert} (hc : Check.Cont C C.cuts.length) {i x : ℕ} (h : cellW C i = some x) :
    C.locs.getD i 0 = x := by
  unfold cellW at h
  simp only [Bool.cond_eq_ite, Bool.and_eq_true, Nat.ble_eq] at h
  split_ifs at h with hw
  obtain ⟨hm, hxe⟩ := List.getElem?_eq_some_iff.mp h
  have hloc := Check.cont_locs hc hw.1 hm
  rwa [Nat.add_sub_cancel' hw.2, hxe] at hloc

theorem fsN_pos (j : ℕ) : 0 < fsN j := by
  unfold fsN
  cases Nat.beq j 1
  · simp
  · simp [mainFrame, Data.mainCells, Data.jtSlots]

theorem numbered_eq {x : V} (h : numbered x = true) : x = V.n x.idx := by
  obtain ⟨path, tag, idx⟩ := x
  simp only [numbered, Bool.and_eq_true, List.isEmpty_iff, Nat.beq_eq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

end

end LeanVM.Guest.Bridge
