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
public import LeanVM.Guest.Bridge.ProgAl
public import LeanVM.Guest.Bridge.JumpCellsIdx

/-!
# The jump cells of the deployed guest

`AShape A`: the alignment contexts of `A` are the data's (`AlignCtx.ofData` over function `j`'s certificate cells, `Plumb`, entry, whether it is `main`, the guest's powers and jump table), their hint-only cells only values without a certificate cell (below `2`), their code the compiled function's. `jcData j` (`JumpCellsIdx.lean`): `jcDataD` on function `j`'s data, which the kernel decides for every function (`Bridge/JumpCells/`). `ChainArm`: at a chained `match`'s table jump, the arm the previous selector took is one whose target cell the jump reads, what the alignment check cannot see (the chained `match` follows the previous one, its jump repeated at the end of each arm); only `main_loop2` has chains (`B2C.chained_only`).

`jumpCells_of`: on the honest tree and a memory covering its writes, under `ProgAl`, `AShape`, every function's `jcData` and `ChainArm`, the top frame of every state of the track against the run has its jump cells (`JumpCells`), each from what its frame holds (`FrameHolds`, `RefOk.frames`): the fixed cells' constants and frame words, a condition at its certificate cell (`walk_inK`, `locAt_ofData`), a table jump's target through the jump table (`tbl_armWord`), a call site's callee frame and header (the site the check names `siteOf`'s, no two sites of one argument list; a loop helper's last call no site's, `loop_last`), a loop's tail call to the frame right after its own (`FrameHolds.tail`), its header; `main` at frame `0` (no path calls `main`, `insts_main`) and only `main` (`Memory.insts_same`).
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

variable {hdr : E × E} {rd rd0 : Reader} {T : Tree} {κ : ℕ} {L : MemoryImage κ} {M : ℕ → E}

/-- **The jump cells of the deployed guest**: the top frame of every state of the track against the
run holds what its jumps read, on a memory covering the honest writes. -/
theorem jumpCells_of (hT : T.name = "main") (hH : HonestAt coreProgram B2C.fs B2C.H B2C.C hdr T B2C.cert rd [] [])
    (hL : Covers coreProgram B2C.fs B2C.H B2C.C hdr T L)
    (hD : ∀ j, 1 ≤ j → j < nFns → jcData j = true)
    (hCh : ChainArm rd0 (honestInsts coreProgram B2C.fs B2C.H hdr T) T M alignA) {pc fp : ℕ} {done : List Pop}
    {e : Ent} {st : List Ent}
    (h : RefOk coreProgram rd0 (honestInsts coreProgram B2C.fs B2C.H hdr T) T M (entOf alignA) (alOf alignA) pc fp
      (done, e :: st)) : JumpCells L alignA e pc := by
  obtain ⟨hIe, j, bufs, kids, vs, hj, ht, hcore, hw, hF⟩ := h.frames hT hH hL e List.mem_cons_self
  have hE := h.track.ents e List.mem_cons_self
  obtain ⟨i0, rfl, -, -, -, -, hfs, -, h1, h2⟩ := fn_of_idx hj
  have hA : alignA e.I.t.name = fnAl (i0 + 1) := alignA_of hj
  have hd := hD _ h1 h2
  unfold jcData jcDataD at hd
  simp only [Bool.and_eq_true] at hd
  obtain ⟨⟨⟨⟨⟨⟨⟨hstat, harms⟩, hsites⟩, huniq⟩, hextra⟩, hblock⟩, hloop⟩, hnext⟩ := hd
  have hcont := Check.cont_of (End.winOk_of h1 h2)
  have hwc : walk e.σ (coreOf (i0 + 1)).body = .ret (e.pre ++ e.es) vs := by rw [hcore]; exact hw
  have hes : ∀ es' vs', walk e.σ e.fn.body = .ret es' vs' → es' = e.pre ++ e.es := fun es' vs' h' ↦ by
    rw [hw] at h'; exact (Out.ret.inj h').1.symm
  have hstatB : ∀ {o : ℕ} {w : PC}, (o, w) ∈ (plumbOf (i0 + 1)).stat →
      cellAt L e.I.fp o = some (w.word e.I.fp) ∧ (∀ a b, w = .k a b → a < 2 ^ 64 ∧ b < 2 ^ 64) := by
    intro o w hm
    have hb := List.all_eq_true.mp hstat _ hm
    simp only [cellIn, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hb
    refine ⟨hF.stat _ hm hb.1.1 hb.1.2, fun a b hw' ↦ ?_⟩
    subst hw'
    simpa only [Bool.and_eq_true, Nat.blt_eq] using hb.2
  have hroot : ∀ I ∈ honestInsts coreProgram B2C.fs B2C.H hdr T, I.t.name = "main" → I.fp = 0 := fun I hI hn ↦ by
    rcases insts_main_or T _ hdr hH.toHonest.valid I hI with ⟨h0, -⟩ | h0
    · exact h0
    · exact absurd hn h0
  have hmain : (i0 + 1 == 1) = true → e.I.fp = 0 := fun h1' ↦
    hroot _ hIe ((idx_one_iff hj).mp (by simpa using h1'))
  have hok := progAl.ok _ _ hE.find
  rw [hA] at hok
  have hlocs : (certOf (i0 + 1)).locs.all (fun c ↦ Nat.blt c (2 ^ cellBits)) = true := by
    rw [alignOk, AlignCtx.seq_eq] at hok
    simp only [Bool.and_eq_true] at hok
    exact hok.1.1.1.1
  have hfe : e.I.fp = 0 → e.I.Frame B2C.fs 0 := fun h0 ↦
    ⟨by omega, by rw [hfs]; have := fsN_pos (i0 + 1); omega⟩
  have hf0 : ∀ {I : Inst}, I.t = T → I.fp = 0 → I.Frame B2C.fs 0 := fun {I} hIt h0 ↦ by
    obtain ⟨-, -, -, -, -, -, hfs1, -⟩ := fn_of_idx idxOf_main
    refine ⟨by omega, ?_⟩
    rw [hIt, hT, hfs1]
    have := fsN_pos 1
    omega
  refine ⟨?zero, ?nz, ?self, ?pcw, ?cond, ?arm, ?site, ?tail, ?hdr, ?main, ?bot⟩
  case zero =>
    intro o hz
    rw [hA] at hz
    unfold AlignCtx.zeroAt at hz
    split at hz
    · rename_i k0 k1 hso
      simp only [Bool.and_eq_true, Nat.beq_eq] at hz
      obtain ⟨rfl, rfl⟩ := hz
      rw [(hstatB (statOf_ofData hso)).1]
      simp [PC.word, Mode.imm_zero]
    · cases hz
  case nz =>
    intro o hz
    rw [hA] at hz
    unfold AlignCtx.nzAt at hz
    split at hz
    · rename_i k0 k1 hso
      obtain ⟨hr, hk⟩ := hstatB (statOf_ofData hso)
      obtain ⟨ha, hb⟩ := hk k0 k1 rfl
      refine ⟨_, hr, Mode.imm_ne_zero ha hb fun ⟨h0, h1⟩ ↦ ?_⟩
      subst h0 h1
      simp at hz
    · cases hz
  case self =>
    intro o hz
    rw [hA] at hz
    unfold AlignCtx.selfAt at hz
    split at hz
    · rename_i hso
      rw [(hstatB (statOf_ofData hso)).1]
      simp [PC.word]
    · rename_i hso
      rw [(hstatB (statOf_ofData hso)).1, hmain hz]
      simp only [PC.word, imm_one, addressOfIndex, pow_zero, Exec.ofK_one]
    · cases hz
  case pcw =>
    intro o t hz
    rw [hA] at hz
    unfold AlignCtx.pcAt at hz
    split at hz
    · rename_i k0 hso
      rw [(hstatB (statOf_ofData hso)).1]
      simp only [PC.word]
      rw [Exec.imm_of_ofBits (Mode.PowTree.find_ok' (Exec.PowTree.ok_of_okW Checked.powTree_ok) hz)]
    · cases hz
  case cond =>
    intro c es' vs' hw' hc
    obtain rfl := hes es' vs' hw'
    have hcc : c ∈ condsOf (coreOf (i0 + 1)).body := walk_inK _ (by rw [hwc, evsOf_ret]; exact hc)
    have hco := blockB_conds _ _ hblock c hcc
    unfold condOk at hco
    simp only [Bool.and_eq_true, Nat.blt_eq] at hco
    obtain ⟨hidx, hxc⟩ := hco
    split at hxc
    · rename_i x hxs
      have hloc := cellW_spec hcont hxs
      simp only [cellIn, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hxc
      have hval := hF.val c (List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨_, hc, by simp [Ev.uses]⟩))) (by rw [cellJ, hloc]; exact hxc.1)
        (by rw [cellJ, hloc]; exact hxc.2)
      have hxn : (extraOf (i0 + 1)).lookup c.idx = none := by
        cases hl : (extraOf (i0 + 1)).lookup c.idx with
        | none => rfl
        | some c' =>
          have hm := mem_of_lookupN hl
          have := List.all_eq_true.mp hextra _ hm
          split at this
          · rename_i y hy
            rw [cellW_spec hcont hy] at hloc
            simp only [Nat.blt_eq] at this
            omega
          · cases this
      have hla : (fnAl (i0 + 1)).X.locAt c.idx = (certOf (i0 + 1)).locs.getD c.idx 0 :=
        locAt_ofData hlocs hxn hidx
      rw [hA, hla]
      exact hval
    · cases hxc
  case arm =>
    intro off oc od of hpc hcode bs x arms ps hpos a ha hax k t hσk ht'
    rw [hA] at ha ht'
    -- the selector is numbered: the `match` is a statement of the body
    have hnum : x = V.n x.idx := by
      obtain ⟨-, off0, -, p0, hal0, as0, -, hpos0⟩ := h.linked.top
      rw [alOf, hA] at hal0
      simp only [alignAt] at hal0
      obtain ⟨c0, hl0, rfl⟩ := Option.map_eq_some_iff.mp hal0
      obtain ⟨l, hl, hlk⟩ := Option.bind_eq_some_iff.mp hl0
      have hpre : alignPre (fnAl (i0 + 1)).X (fnAl (i0 + 1)).d = true := by
        rw [alignOk, AlignCtx.seq_eq] at hok
        simp only [Bool.and_eq_true] at hok
        simp only [alignPre, Bool.and_eq_true]
        exact ⟨⟨⟨hok.1.1.1.1, hok.1.1.1.2⟩, hok.1.1.2⟩, hok.1.2⟩
      obtain ⟨-, -, -, -, -, -, hz0, -⟩ := alignRun_step hpre hl (mem_of_lookup hlk)
      have hmem : Stmt.match_ x arms ∈ c0.pos := by
        have : Stmt.match_ x arms ∈ e.pos := by rw [hpos]; simp
        rw [hpos0, List.mem_append] at this
        rcases this with h' | h'
        · simp at h'
        · exact h'
      exact numbered_eq (blockB_sels _ _ hblock _ (zok_stmts hz0 hmem) x arms rfl)
    have hσx : e.σ (V.n a.1) = ofK (addressOfIndex k) := by rw [hax, ← hnum]; exact hσk
    have hjt := End.jtHolds_of (jumpTables_cover hH.toHonest hL hT)
    have htab := jumpTables_cover hH.toHonest hL hT
    have hglob : glob.jt.get (a.2 + k) = some t := by
      change Data.jtTrie.get (a.2 + k) = some t
      rw [← getF_eq]; exact ht'
    obtain ⟨hf, hlt⟩ := tbl_slot hjt htab hglob
    have hword := tbl_armWord hσx hf hlt
    have hmem := arms_ofData ha
    have hb := List.all_eq_true.mp harms _ hmem
    simp only [cellIn, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hb
    unfold armsOf at hmem
    rcases List.mem_append.mp hmem with hm | hm
    · obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hm
      simp only [Prod.mk.injEq] at hqe
      obtain ⟨rfl, rfl⟩ := hqe
      rw [cellAt, hF.arm q hq hb.1 hb.2]
      exact congrArg some hword
    · obtain ⟨ch, hch, hm'⟩ := List.mem_flatMap.mp hm
      obtain ⟨t', ht'', hte⟩ := List.mem_map.mp hm'
      simp only [Prod.mk.injEq] at hte
      obtain ⟨rfl, rfl⟩ := hte
      obtain ⟨k', hk', hσ'⟩ := hCh _ _ _ _ _ h _ hj off oc t' of hpc hcode ch hch ht''
      obtain ⟨-, -, -, -, hread⟩ := hF.chain ch hch k' t' hk' hσ'
      rw [cellAt, hread hb.1 hb.2]
      exact congrArg some hword
  case site =>
    intro es' vs' hw' i c q s hc htk hs
    obtain rfl := hes es' vs' hw'
    rw [hA] at hs
    obtain ⟨hsm, hsq, hsa, hsr⟩ := siteAt_ofData hs
    have hso : siteOf (i0 + 1) c = some s := siteOf_eq huniq hsm hsa hsr
    have hi : i < (calls (e.pre ++ e.es)).length := (List.getElem?_eq_some_iff.mp hc).1
    obtain ⟨kfp, hkfp⟩ : ∃ kfp, e.I.kidFps[i]? = some kfp :=
      ⟨_, List.getElem?_eq_getElem (by rw [hF.len]; exact hi)⟩
    obtain ⟨hq', htg⟩ := hF.site i c kfp s hc hkfp hso
    obtain ⟨hk0, hk1, -, -⟩ := hF.kid i c kfp hc hkfp
    have hnl : ¬((coreOf (i0 + 1)).loop = true ∧ i + 1 = (calls (e.pre ++ e.es)).length) := by
      rintro ⟨hl, hi'⟩
      simp only [hl, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hloop
      exact loop_last hloop.2 hwc hc hi' s hsm ⟨hsa, hsr⟩
    have hkh : kidHdr (i0 + 1) e.I.fp e.I.hdr (e.pre ++ e.es) i =
        (ofK (addressOfIndex s.r), ofK (addressOfIndex e.I.fp)) := by
      unfold kidHdr
      rw [hc]
      dsimp only
      rw [ite_eq_right hnl, hso]
    have hb := List.all_eq_true.mp hsites _ hsm
    simp only [cellIn, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Bool.or_eq_true, beq_iff_eq] at hb
    refine ⟨kfp, hkfp, ?_, ?_, ?_, fun htg0 ↦ ?_⟩
    · rw [← hsq]; exact hq' hb.1.1 hb.1.2
    · rw [cellAt, hk0, hkh]
    · rw [cellAt, hk1, hkh]
    · rcases hb.2 with h0 | hb2
      · exact absurd h0 htg0
      obtain ⟨rv, hkv⟩ := hE.kids
      obtain ⟨kk, -, hkn, hkv'⟩ := kidsValid_get hkv hc
      obtain ⟨args, rets, hv⟩ := hkv' htk
      rcases kk with ⟨f', σ', bufs', kids'⟩ | ⟨f', σ'⟩
      · obtain ⟨fn', hf', -⟩ := hv
        simp only [Tree.name] at hkn
        subst hkn
        obtain ⟨j', hj'⟩ := idxOf_of_find hf'
        rw [cellAt, htg htg0 hb2.1 hb2.2, entryOf_of hj', alignA_of hj']
        rfl
      · exact hv.elim
  case tail =>
    intro off oc od q hpc hcode hnx es' vs' hw' i c hc htk hi
    obtain rfl := hes es' vs' hw'
    rw [hA] at hnx hcode
    unfold AlignCtx.nextAt at hnx
    split at hnx
    · rename_i S hso
      have hm := statOf_ofData hso
      have hS : S ≠ 0 := fun h0 ↦ by simp [h0] at hnx
      have hls : (coreOf (i0 + 1)).loop = true ∧ S = fsN (i0 + 1) := by
        rcases Bool.or_eq_true _ _ |>.mp hnext with hn | hn
        · have := List.all_eq_true.mp hn _ hm
          simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at this
          rcases this with h0 | h0
          · exact absurd h0 hS
          · exact h0
        · have hmem : OffsetInstruction.jump oc od q ∈ (fnOf (i0 + 1)).code := List.mem_of_getElem? hcode
          have := List.all_eq_true.mp (List.all_eq_true.mp hn _ hmem) _ hm
          simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq,
            Bool.and_eq_true] at this
          rcases this with h0 | h0
          · exact absurd h0 hS
          · exact h0
      have hn1 : (i0 + 1 == 1) = false := by
        have := hloop
        simp only [hls.1, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at this
        exact this.1
      have hi' : i < (calls (e.pre ++ e.es)).length := (List.getElem?_eq_some_iff.mp hc).1
      obtain ⟨kfp, hkfp⟩ : ∃ kfp, e.I.kidFps[i]? = some kfp :=
        ⟨_, List.getElem?_eq_getElem (by rw [hF.len]; exact hi')⟩
      have hlast : e.I.kidFps.getLast? = some kfp := by
        rw [List.getLast?_eq_getElem?, hF.len, ← hi, Nat.add_sub_cancel]; exact hkfp
      have hkv := hF.tail hls.1 kfp hlast
      obtain ⟨hk0, hk1, -, -⟩ := hF.kid i c kfp hc hkfp
      have hkh : kidHdr (i0 + 1) e.I.fp e.I.hdr (e.pre ++ e.es) i = e.I.hdr := by
        unfold kidHdr
        rw [hc]
        dsimp only
        rw [ite_eq_left ⟨hls.1, hi⟩]
      refine ⟨fun h0 ↦ ?_, kfp, hkfp, ?_, ?_, ?_⟩
      · obtain ⟨I0, hI0, hI0t, hI0fp, -⟩ := root_inst (P := coreProgram) (fs := B2C.fs) (H := B2C.H) (hdr := hdr) (T := T)
        have := insts_same hIe hI0 (hfe h0) (hf0 hI0t hI0fp)
        have hn : e.I.t.name = "main" := by rw [this, hI0t, hT]
        have := (idx_one_iff hj).mpr hn
        simp [this] at hn1
      · rw [(hstatB hm).1, hkv]
        simp only [PC.word, hls.2]
      · rw [cellAt, cellAt, hk0, hkh, hF.hdr0]
      · rw [cellAt, cellAt, hk1, hkh, hF.hdr1]
    · cases hnx
  case hdr =>
    refine ⟨?_, ?_⟩
    · rw [cellAt, hF.hdr0]; rfl
    · rw [cellAt, hF.hdr1]; rfl
  case main =>
    intro hm
    rw [hA] at hm
    exact hmain hm
  case bot =>
    intro h0
    obtain ⟨I0, hI0, hI0t, hI0fp, -⟩ := root_inst (P := coreProgram) (fs := B2C.fs) (H := B2C.H) (hdr := hdr) (T := T)
    have := insts_same hIe hI0 (hfe h0) (hf0 hI0t hI0fp)
    have hn : e.I.t.name = "main" := by rw [this, hI0t, hT]
    have h01 : i0 + 1 = 1 := (idx_one_iff hj).mpr hn
    rw [hA]
    show (i0 + 1 == 1) = true
    rw [h01]; rfl

end

end LeanVM.Guest.Bridge
