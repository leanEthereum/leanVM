/-
  LeanVM.Guest.CoreMode.Fn.link_rounds.LrChain

  `link_rounds`' loops at the honest instances of b2c's aligned tree (`LrQ`): each iteration's record holds the
  cursor `4W` words a round further, carried down from `link_rounds`; so their reads lie in the run past `cursor`
  below the exponent of `count_g` (`lr_stOk`, the cursor-run family's `StLoopOkA`).
-/

module

public import LeanVM.Guest.EndExecCoreStA
public import LeanVM.Guest.EndExecCoreResA
public import LeanVM.Guest.CoreMode.Fn.child_claim_list_mono.ResM
public import LeanVM.Guest.CoreMode.Fam.ProgOkG
public import LeanVM.Guest.CoreMode.Gen.TermCallers
public import LeanVM.Guest.B1.Link.RoundsLoop
public import LeanVM.Guest.B1.Link.RoundsSound
public import LeanVM.Guest.CoreMode.Fn.link_rounds.Data

/-!
# `link_rounds`' loops down the honest tree

`link_rounds__L{t}_L{b}` splits `count_g = g^(4h + r)` (`h < 16`, `r < 4`), stores its record (the sponge, the
`cursor`, the claim) at `recs` and calls its loop `link_rounds__L{t}_L{b}_loop0(x, h_g, recs, point, tabs)` from
`x = g^0`; an iteration at `x = g^j` runs four rounds from the record at `recs·g^(7j)`, each moving the cursor
`W = t + 1 + [b > 0]` words (`lrRounds_cur`), stores the next record at `recs·g^(7(j + 1))` and calls itself at `g^(j+1)`
while `g^(j+1) ≠ h_g`. `LrQ r J`: at an instance of the loop, its header names `link_rounds`' frame `a`, whose cell `10`
holds `g^n`, `4h ≤ n < 64`, its counter `g^j`, `j < h`, and its record's cursor the word at the frame's cell `7` times
`g^(4Wj)`. `lrQ_allA` by `insts_allA`: from `link_rounds` (its atoms, `lrLoop_pos`), and down a tail call (the
iteration's atoms). `lr_stOk`: the cursor-run family's `StLoopOkA` for the loops' entries.
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Protocol.Verifier (gen)

public section

/-- A round's cursor atoms: `g^W` as a constant, the cursor times it, its copy. -/
theorem lrRound_curMem (nt bits o : ℕ) (cap : List ℕ) (cur cl tabs : ℕ) (pad : Option ℕ) :
    Stmt.atom (.const (.n (lrD o nt bits pad + 4)) (word (2 ^ (nt + 1 + if bits = 0 then 0 else 1)) 0)) ∈
        lrRound nt bits o cap cur cl tabs pad ∧
      Stmt.atom (.mul (.n (lrD o nt bits pad + 5)) (.n cur) (.n (lrD o nt bits pad + 4))) ∈
        lrRound nt bits o cap cur cl tabs pad ∧
      Stmt.atom (.copy (.n (lrD o nt bits pad + 6)) (.n (lrD o nt bits pad + 5))) ∈
        lrRound nt bits o cap cur cl tabs pad := by
  refine ⟨?_, ?_, ?_⟩ <;> (simp only [lrRound]; exact List.mem_append_right _ (by simp))

/-- **The cursor after `k` rounds** is the first one `k·W` words on, `W = nt + 1 + [bits > 0]`, by the rounds'
cursor atoms alone. -/
theorem lrRounds_cur {rd : Reader} {σ : Val} {nt bits pts tabs : ℕ}
    (hW : nt + 1 + (if bits = 0 then 0 else 1) < 64) :
    ∀ (k o : ℕ) (cap : List ℕ) (cur cl : ℕ) (pad : Option ℕ),
      (∀ a, Stmt.atom a ∈ (lrRounds nt bits pts tabs k o cap cur cl pad).1 → a.Holds rd σ) →
      σ (.n (lrRounds nt bits pts tabs k o cap cur cl pad).2.2.1) =
        σ (.n cur) * gen ^ (k * (nt + 1 + if bits = 0 then 0 else 1))
  | 0, _, _, _, _, _, _ => by simp [lrRounds]
  | k + 1, o, cap, cur, cl, pad, h => by
    rw [lrRounds_succ] at h ⊢
    dsimp only at h ⊢
    have ih := lrRounds_cur hW k o cap cur cl pad
      (fun a ha ↦ h a (List.mem_append_left _ (List.mem_append_left _ ha)))
    obtain ⟨m1, m2, m3⟩ := lrRound_curMem nt bits (lrRounds nt bits pts tabs k o cap cur cl pad).2.2.2.2.1
      (lrRounds nt bits pts tabs k o cap cur cl pad).2.1 (lrRounds nt bits pts tabs k o cap cur cl pad).2.2.1
      (lrRounds nt bits pts tabs k o cap cur cl pad).2.2.2.1 tabs
      (lrRounds nt bits pts tabs k o cap cur cl pad).2.2.2.2.2
    have a1 := h _ (List.mem_append_left _ (List.mem_append_right _ m1))
    have a2 := h _ (List.mem_append_left _ (List.mem_append_right _ m2))
    have a3 := h _ (List.mem_append_left _ (List.mem_append_right _ m3))
    simp only [Atom.Holds] at a1 a2 a3
    rw [a3, a2, a1, ih, word_two_pow hW, mul_assoc, ← pow_add, add_one_mul]

end

end LeanVM.Guest.B1.Link

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf FrameHolds fsN fn_of_idx cellJ namedOf kidHdr siteOf)
open LeanVM.Guest.Value (gen_pow_eq_ofK gen_pow_inj)
open LeanVM.Guest.B1.Digest (find_of_idx)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

@[expose] public section

/-- The words a round of `link_round` reads: `c0`, the `nt` tail coefficients and, with a grind, its nonce. -/
def lrW (nt bits : ℕ) : ℕ := nt + 1 + if bits = 0 then 0 else 1

/-- **`link_rounds`' specializations**: `n_tail`, `bits`, the function, its loop. -/
def lrSpecs : List (ℕ × ℕ × String × String) :=
  [(1, 0, name% «link_rounds__L1_L0», name% «link_rounds__L1_L0_loop0»),
    (6, 0, name% «link_rounds__L6_L0», name% «link_rounds__L6_L0_loop0»),
    (7, 0, name% «link_rounds__L7_L0», name% «link_rounds__L7_L0_loop0»),
    (8, 1, name% «link_rounds__L8_L1», name% «link_rounds__L8_L1_loop0»),
    (9, 1, name% «link_rounds__L9_L1», name% «link_rounds__L9_L1_loop0»),
    (10, 1, name% «link_rounds__L10_L1», name% «link_rounds__L10_L1_loop0»)]

/-- **What a specialization's facts are**: its loop's shape (`lrLoopBody`), its body (`lrMainBody`), its frame cells
`7`, `10` holding `cursor`, `count_g`, its call of the loop at its site, the loop's callers. -/
structure LrSpec (nt bits : ℕ) (main loop : String) : Prop where
  w : lrW nt bits < 64
  loopF : ∃ fL : Fn, coreProgram.find? loop = some fL ∧ fL.loop = true ∧ Res.endOfFn fL = some none ∧
    fL.params = [.n 0, .n 1, .n 2, .n 3, .n 4] ∧ fL.body = B1.Link.lrLoopBody nt bits loop
  mainF : ∃ (fM : Fn) (jm : ℕ) (lasts : List String), coreProgram.find? main = some fM ∧ idxOf main = some jm ∧
    fM.body = B1.Link.lrMainBody loop lasts ∧ fM.loop = false ∧ V.n 5 ∈ fM.params ∧ V.n 8 ∈ fM.params ∧
    cellJ jm (.n 5) = 7 ∧ cellJ jm (.n 8) = 10 ∧ 10 < fsN jm ∧
    Res.sitesB (fun g args rets ↦ g != loop || (args == [.n 56, .n 43, .n 53, .n 7, .n 9] && Res.siteB jm args rets))
      fM.body = true
  callers : (loop, main) ∈ Res.termCallers

end

public section

set_option maxRecDepth 100000 in
theorem lrSpec_L1_L0 : LrSpec 1 0 name% «link_rounds__L1_L0» name% «link_rounds__L1_L0_loop0» :=
  ⟨by decide, ⟨fn% «link_rounds__L1_L0_loop0», coreProgram_find?_at (j := idx% «link_rounds__L1_L0_loop0») rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, B1.Link.lrLoop_L1_L0_body⟩,
    ⟨fn% «link_rounds__L1_L0», fn_idx% «link_rounds__L1_L0», _,
      coreProgram_find?_at (j := idx% «link_rounds__L1_L0») rfl, by decide +kernel, B1.Link.lrMain_L1_L0_body,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel⟩, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem lrSpec_L6_L0 : LrSpec 6 0 name% «link_rounds__L6_L0» name% «link_rounds__L6_L0_loop0» :=
  ⟨by decide, ⟨fn% «link_rounds__L6_L0_loop0», coreProgram_find?_at (j := idx% «link_rounds__L6_L0_loop0») rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, B1.Link.lrLoop_L6_L0_body⟩,
    ⟨fn% «link_rounds__L6_L0», fn_idx% «link_rounds__L6_L0», _,
      coreProgram_find?_at (j := idx% «link_rounds__L6_L0») rfl, by decide +kernel, B1.Link.lrMain_L6_L0_body,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel⟩, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem lrSpec_L7_L0 : LrSpec 7 0 name% «link_rounds__L7_L0» name% «link_rounds__L7_L0_loop0» :=
  ⟨by decide, ⟨fn% «link_rounds__L7_L0_loop0», coreProgram_find?_at (j := idx% «link_rounds__L7_L0_loop0») rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, B1.Link.lrLoop_L7_L0_body⟩,
    ⟨fn% «link_rounds__L7_L0», fn_idx% «link_rounds__L7_L0», _,
      coreProgram_find?_at (j := idx% «link_rounds__L7_L0») rfl, by decide +kernel, B1.Link.lrMain_L7_L0_body,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel⟩, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem lrSpec_L8_L1 : LrSpec 8 1 name% «link_rounds__L8_L1» name% «link_rounds__L8_L1_loop0» :=
  ⟨by decide, ⟨fn% «link_rounds__L8_L1_loop0», coreProgram_find?_at (j := idx% «link_rounds__L8_L1_loop0») rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, B1.Link.lrLoop_L8_L1_body⟩,
    ⟨fn% «link_rounds__L8_L1», fn_idx% «link_rounds__L8_L1», _,
      coreProgram_find?_at (j := idx% «link_rounds__L8_L1») rfl, by decide +kernel, B1.Link.lrMain_L8_L1_body,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel⟩, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem lrSpec_L9_L1 : LrSpec 9 1 name% «link_rounds__L9_L1» name% «link_rounds__L9_L1_loop0» :=
  ⟨by decide, ⟨fn% «link_rounds__L9_L1_loop0», coreProgram_find?_at (j := idx% «link_rounds__L9_L1_loop0») rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, B1.Link.lrLoop_L9_L1_body⟩,
    ⟨fn% «link_rounds__L9_L1», fn_idx% «link_rounds__L9_L1», _,
      coreProgram_find?_at (j := idx% «link_rounds__L9_L1») rfl, by decide +kernel, B1.Link.lrMain_L9_L1_body,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel⟩, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem lrSpec_L10_L1 : LrSpec 10 1 name% «link_rounds__L10_L1» name% «link_rounds__L10_L1_loop0» :=
  ⟨by decide, ⟨fn% «link_rounds__L10_L1_loop0», coreProgram_find?_at (j := idx% «link_rounds__L10_L1_loop0») rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, B1.Link.lrLoop_L10_L1_body⟩,
    ⟨fn% «link_rounds__L10_L1», fn_idx% «link_rounds__L10_L1», _,
      coreProgram_find?_at (j := idx% «link_rounds__L10_L1») rfl, by decide +kernel, B1.Link.lrMain_L10_L1_body,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel⟩, by decide +kernel⟩

/-- Every specialization's facts. -/
theorem lrSpec_all {nt bits : ℕ} {main loop : String} (h : (nt, bits, main, loop) ∈ lrSpecs) :
    LrSpec nt bits main loop := by
  simp only [lrSpecs, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · exact lrSpec_L1_L0
  · exact lrSpec_L6_L0
  · exact lrSpec_L7_L0
  · exact lrSpec_L8_L1
  · exact lrSpec_L9_L1
  · exact lrSpec_L10_L1

theorem lrSpecs_not_main : ∀ e ∈ lrSpecs, e.2.2.2 ≠ "main" := by decide

/-- An atom of an all-atoms prefix is a top-level atom. -/
theorem mem_topAtoms_of {a : Atom} : ∀ {ss : List Stmt} (rest : List Stmt), B1.AllAtoms ss → Stmt.atom a ∈ ss →
    a ∈ Res.topAtoms (ss ++ rest)
  | [], _, _, h => by simp at h
  | s :: ss, rest, hA, h => by
    obtain ⟨b, rfl⟩ := hA s List.mem_cons_self
    have hA' : B1.AllAtoms ss := fun t ht ↦ hA t (List.mem_cons_of_mem _ ht)
    rw [List.cons_append, Res.topAtoms]
    rcases List.mem_cons.mp h with h | h
    · cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_topAtoms_of rest hA' h)

/-- An all-atoms block calls nothing. -/
theorem blockCallees_atoms : ∀ {ss : List Stmt}, B1.AllAtoms ss → Stmt.blockCallees ss = []
  | [], _ => rfl
  | s :: ss, hA => by
    obtain ⟨b, rfl⟩ := hA s List.mem_cons_self
    simp only [Stmt.blockCallees, Stmt.callees, List.nil_append]
    exact blockCallees_atoms fun t ht ↦ hA t (List.mem_cons_of_mem _ ht)

/-- **The loop's atoms hold** on a returning path of its body. -/
theorem lrLoop_atoms {rd : Reader} {σ : Val} {nt bits : ℕ} {loop : String} {fL : Fn}
    (hb : fL.body = B1.Link.lrLoopBody nt bits loop) {es : List Ev} {vs : List V}
    (hw : walk σ fL.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ) :
    ∀ a, Stmt.atom a ∈ B1.Link.lrLoopA nt bits → a.Holds rd σ := by
  intro a ha
  have hm : a ∈ Res.topAtoms fL.body := by
    rw [hb, B1.Link.lrLoopBody_eq]
    exact mem_topAtoms_of _ (B1.Link.lrLoopA_atoms nt bits) ha
  exact hh _ (topAtoms_on_path hw hm)

/-- **What an iteration's atoms give**: its record at `recs·x^7`, the cursor read there, and the cursor `4W` words on
stored seven cells further. -/
theorem lrIter {rd : Reader} {σ : Val} {nt bits : ℕ} (hW : lrW nt bits < 64)
    (hA : ∀ a, Stmt.atom a ∈ B1.Link.lrLoopA nt bits → a.Holds rd σ) :
    σ (.n 9) = σ (.n 2) * σ (.n 0) ^ 7 ∧ LoadHolds rd (σ (.n 9)) 5 (σ (.n 18)) ∧
      LoadHolds rd (σ (.n 9)) 12 (σ (.n 18) * gen ^ (4 * lrW nt bits)) := by
  have mem : ∀ a ∈ [Atom.mul (.n 5) (.n 0) (.n 0), .mul (.n 6) (.n 5) (.n 0), .mul (.n 7) (.n 6) (.n 6),
      .mul (.n 8) (.n 7) (.n 0), .mul (.n 9) (.n 2) (.n 8), .load (.n 18) (.n 9) 5], a.Holds rd σ := fun a ha ↦
    hA a (by
      unfold B1.Link.lrLoopA
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  have m5 := mem _ (by simp : Atom.mul (.n 5) (.n 0) (.n 0) ∈ _)
  have m6 := mem _ (by simp : Atom.mul (.n 6) (.n 5) (.n 0) ∈ _)
  have m7 := mem _ (by simp : Atom.mul (.n 7) (.n 6) (.n 6) ∈ _)
  have m8 := mem _ (by simp : Atom.mul (.n 8) (.n 7) (.n 0) ∈ _)
  have m9 := mem _ (by simp : Atom.mul (.n 9) (.n 2) (.n 8) ∈ _)
  have l18 := mem _ (by simp : Atom.load (.n 18) (.n 9) 5 ∈ _)
  simp only [Atom.Holds] at m5 m6 m7 m8 m9 l18
  have hrs : ∀ a, Stmt.atom a ∈ (B1.Link.lrLoopRounds nt bits).1 → a.Holds rd σ := fun a ha ↦
    hA a (by
      unfold B1.Link.lrLoopA
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ha)))
  have hcur := B1.Link.lrRounds_cur (rd := rd) (σ := σ) (pts := 12) (tabs := 4) hW 4 20 [13, 14, 15, 16, 17] 18 19
    none hrs
  have l12 := hA (.load (.n (B1.Link.lrLoopRounds nt bits).2.2.1) (.n 9) 12) (by
    unfold B1.Link.lrLoopA
    exact List.mem_append_right _ (by simp))
  simp only [Atom.Holds] at l12
  refine ⟨by rw [m9, m8, m7, m6, m5]; ring, l18, ?_⟩
  have e : σ (.n (B1.Link.lrLoopRounds nt bits).2.2.1) = σ (.n 18) * gen ^ (4 * lrW nt bits) := hcur
  rwa [e] at l12

variable {al : String → Bool} {D : Ref → RefD} {r : Ref}

/-- **A loop of `link_rounds` runs at least once**: entered at `g^0` with its end `g^a`, `a < 2^32`, then `a ≥ 1`. -/
theorem lrLoop_pos {rd : Reader} {f : String} {fL : Fn} (hf : coreProgram.find? f = some fL) (hl : fL.loop = true)
    (hend : Res.endOfFn fL = some none) (hpar : fL.params = [.n 0, .n 1, .n 2, .n 3, .n 4]) {σ : Val}
    {bufs : List ℕ} {kids : List Tree} {args rets : List E}
    (hv : (Memory.Tree.node f σ bufs kids).Valid coreProgram rd args rets)
    (htot : (Memory.Tree.node f σ bufs kids).total B2C.fs ≤ 2 ^ 28) (h0 : σ (.n 0) = 1) {a : ℕ}
    (ha : a < 2 ^ 32) (h1 : σ (.n 1) = gen ^ a) : 1 ≤ a := by
  obtain ⟨-, e, he, hs, -⟩ := progOk_guest.loop f _ hf hl
  obtain rfl : e = none := Option.some.inj (he.symm.trans hend)
  obtain ⟨m, p0, prest, hps, hm1, hmle, hm⟩ := Res.chain Res.fs_pos _ le_rfl hv hf hs
  rw [hpar] at hps
  obtain ⟨rfl, rfl⟩ := List.cons.inj hps
  simp only [Res.endVal, hpar, h0, h1, one_mul, ← gen_pow_eq_ofK] at hm
  have := gen_pow_inj (by omega) (by omega) hm
  omega

end

@[expose] public section

/-- **`link_rounds`' loops at an instance**: the header names `link_rounds`' frame `a`, its cell `10` holding
`g^n`, `4h ≤ n < 64`; the counter `g^j`, `j < h`, the end `g^h`; the record at `recs·g^(7j)` holding at offset `5`
the word at the frame's cell `7` times `g^(4Wj)`. -/
def LrQ (r : Ref) (J : Inst) : Prop :=
  ∀ f σ bufs kids, J.t = .node f σ bufs kids → ∀ nt bits main, (nt, bits, main, f) ∈ lrSpecs →
    ∃ a j h n, J.hdr.2 = ofK (addressOfIndex a) ∧ a + 10 < maxCells ∧ refMem r.img (a + 10) = gen ^ n ∧
      n < 64 ∧ 4 * h ≤ n ∧ σ (.n 0) = gen ^ j ∧ j < h ∧ σ (.n 1) = gen ^ h ∧
      LoadHolds r.img.read (σ (.n 2) * gen ^ (7 * j)) 5 (refMem r.img (a + 7) * gen ^ (4 * lrW nt bits * j))

end

public section

variable {al : String → Bool} {D : Ref → RefD} {r : Ref}

set_option maxHeartbeats 1000000 in
/-- **`LrQ` passes down a call.** -/
theorem lrQ_stepA (hR : RefH (layB al) (D r) r) (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (instsR al D r) (LrQ r) := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ hhdr hname hval hph hQI
    f σ bufs kids hJt nt bits main hmem
  obtain ⟨hW, ⟨fL, hfL, hloop, hend, hparL, hbodyL⟩,
    ⟨fM, jm, lasts, hfM, hjm, hbodyM, hloopM, hm5, hm8, hc5, hc8, hfs, hsites⟩, hcallers⟩ := lrSpec_all hmem
  have hcf : c.f = f := by rw [← hname, hJt]; rfl
  have hct : c.taken = true := by
    cases h : c.taken
    · obtain ⟨g', σ', h'⟩ := hph h
      rw [hJt] at h'; cases h'
    · rfl
  have hJv := hval hct
  rw [hJt] at hJv
  have hJv' := hJv
  obtain ⟨fn, hfn, hpar, -⟩ := hJv'
  obtain rfl : fn = fL := Option.some.inj (hfn.symm.trans hfL)
  rw [hparL] at hpar
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  have hnI : fnI.name = fI := find_name' hfI
  have hJtot : (Memory.Tree.node f σ bufs kids).total B2C.fs ≤ 2 ^ 28 := by
    have := inst_totalA hR hr J hJS; rwa [hJt] at this
  have hcaller : fI = main ∨ (fI = f ∧ fnI.loop = true) := by
    have hcal := List.all_eq_true.mp (Res.calls_sites (Res.termCallers_all fnI (List.mem_of_find?_eq_some hfI))
      hw c hc) _ hcallers
    rw [hcf] at hcal
    simp only [bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcal
    rcases hcal with h | ⟨h, hl⟩
    · exact Or.inl (by rw [← hnI, h])
    · exact Or.inr ⟨by rw [← hnI, h], hl⟩
  rcases hcaller with rfl | ⟨rfl, hl'⟩
  · -- entered from `link_rounds`: its split count, its record, its frame
    obtain rfl : fnI = fM := Option.some.inj (hfI.symm.trans hfM)
    obtain ⟨i', hji, hi', -, hf', hc', -⟩ := fn_of_idx hjm
    have hcj : coreOf jm = fnI := by rw [hc']; exact Option.some.inj (hf'.symm.trans hfI)
    have hs := Res.calls_sites hsites hw c hc
    rw [hcf] at hs
    simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hs
    obtain ⟨hargs, hsb⟩ := hs
    rw [hargs] at hpar
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
    obtain ⟨hp0, hp1, hp2, -, -⟩ := hpar
    obtain ⟨args, rets, hvI⟩ := inst_validA hR hI hIt
    obtain ⟨-, hbI⟩ := Res.holds_of_valid Res.fs_pos hvI hfI
    rw [hbodyM] at hbI
    simp only [B1.Link.lrMainBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
      true_and] at hbI
    obtain ⟨b0, c16, c17, m18, a19, b1, c20, c21, m22, a23, m24, b2, c25, c26, m27, a28, b3, c29, c30,
      m31, a32, m33, b4, c34, c35, m36, a37, m38, b5, c39, c40, m41, a42, m43, m44, m45, m46, hassert,
      -, -, -, -, -, -, -, -, -, -, -, s5, -, c54, a55, c56, -⟩ := hbI
    have w3 : word 3 0 = gen ^ 1 + 1 := B1.Link.word_two_pow_xor_one (a := 1) (by norm_num)
    have w5 : word 5 0 = gen ^ 2 + 1 := B1.Link.word_two_pow_xor_one (a := 2) (by norm_num)
    have w17 : word 17 0 = gen ^ 4 + 1 := B1.Link.word_two_pow_xor_one (a := 4) (by norm_num)
    have w257 : word 257 0 = gen ^ 8 + 1 := B1.Link.word_two_pow_xor_one (a := 8) (by norm_num)
    have hrg : σI (.n 24) = gen ^ (B1.Link.bv (σI (.n 10)) + 2 * B1.Link.bv (σI (.n 11))) := by
      rw [m24, a19, a23, m18, m22, c16, c17, c20, c21, w3, w5, B1.word_one, B1.Link.bit_factor b0,
        B1.Link.bit_factor b1, ← pow_add]
      simp only [B1.Link.bv, one_mul]
    have hqg : σI (.n 43) = gen ^ (B1.Link.bv (σI (.n 12)) + 2 * B1.Link.bv (σI (.n 13)) +
        4 * B1.Link.bv (σI (.n 14)) + 8 * B1.Link.bv (σI (.n 15))) := by
      rw [m43, m38, m33, a28, a32, a37, a42, m27, m31, m36, m41, c25, c26, c29, c30, c34, c35, c39, c40, w3, w5,
        w17, w257, B1.word_one, B1.Link.bit_factor b2, B1.Link.bit_factor b3, B1.Link.bit_factor b4,
        B1.Link.bit_factor b5, ← pow_add, ← pow_add, ← pow_add]
      simp only [B1.Link.bv, one_mul]
    set rv := B1.Link.bv (σI (.n 10)) + 2 * B1.Link.bv (σI (.n 11)) with hrv
    set qv := B1.Link.bv (σI (.n 12)) + 2 * B1.Link.bv (σI (.n 13)) + 4 * B1.Link.bv (σI (.n 14)) +
      8 * B1.Link.bv (σI (.n 15)) with hqv
    have hrv4 : rv < 4 := by
      have := B1.Link.bv_le (σI (.n 10)); have := B1.Link.bv_le (σI (.n 11)); omega
    have hqv16 : qv < 16 := by
      have := B1.Link.bv_le (σI (.n 12)); have := B1.Link.bv_le (σI (.n 13)); have := B1.Link.bv_le (σI (.n 14))
      have := B1.Link.bv_le (σI (.n 15)); omega
    have hcg : σI (.n 8) = gen ^ (4 * qv + rv) := by
      have : σI (.n 8) = σI (.n 46) := by linear_combination hassert.symm + σI (.n 8) * B1.Link.two_eq_zero_E
      rw [this, m46, m45, m44, hqg, hrg]
      ring
    -- the frame's cells
    have hfb := inst_fbA hR hr hI hIt hjm
    have hF0 := inst_frameA hR hI hIt hjm (by rw [hcj]; exact hw)
    have hval' : ∀ u ∈ (coreOf jm).params, 2 ≤ cellJ jm u → cellJ jm u < fsN jm →
        I.fp + cellJ jm u < maxCells ∧ refMem r.img (I.fp + cellJ jm u) = σI u := fun u hu h2 hlt ↦
      ref_readA hr (by omega) (hF0.val u (List.mem_append_left _ (List.mem_append_left _ hu)) h2 hlt)
    obtain ⟨-, hr7⟩ := hval' (.n 5) (by rw [hcj]; exact hm5) (by omega) (by omega)
    obtain ⟨hlt10, hr10⟩ := hval' (.n 8) (by rw [hcj]; exact hm8) (by omega) (by omega)
    rw [hc5] at hr7
    rw [hc8] at hr10 hlt10
    -- the header
    obtain ⟨s, hs'⟩ : ∃ s, siteOf jm c = some s := Option.isSome_iff_exists.mp hsb
    have hH := B2C.H_eq_kidHdr hIt hjm (by rw [hcj]; exact hw) i
    unfold kidHdr at hH
    rw [hci] at hH
    dsimp only at hH
    rw [ite_eq_right (by rw [hcj, hloopM]; simp), hs'] at hH
    -- the loop runs at least once
    have h0 : σ (.n 0) = 1 := by rw [hp0, c56, B1.word_one]
    have h1 : σ (.n 1) = gen ^ qv := by rw [hp1, hqg]
    have hq1 := lrLoop_pos hfL hloop hend hparL hJv hJtot h0 (by omega) h1
    refine ⟨I.fp, 0, qv, 4 * qv + rv, by rw [hhdr, hH], hlt10, by rw [hr10, hcg], by omega, by omega,
      by rw [h0, pow_zero], by omega, h1, ?_⟩
    rw [hp2, hr7]
    simpa using s5
  · -- a tail call: the next iteration
    have hfe : fn = fnI := Option.some.inj (hfn.symm.trans hfI)
    subst hfe
    have hA := lrLoop_atoms hbodyL hw hh
    obtain ⟨h9, l5, l12⟩ := lrIter hW hA
    obtain ⟨-, e0, he0, hsh, -⟩ := progOk_guest.loop fI _ hfI hl'
    obtain rfl : e0 = none := Option.some.inj (he0.symm.trans hend)
    obtain ⟨p0, prest, c0, i0, es1, hps, hw1, hes, hi0, hc0⟩ := Res.loop_path hsh hw hh
    subst hes
    have hlb : Stmt.blockCallees (loopBody fn) = [] := by
      have e : loopBody fn = B1.Link.lrLoopA nt bits := by
        rw [loopBody, hbodyL, B1.Link.lrLoopBody_eq]
        simp
      rw [e]
      exact blockCallees_atoms (B1.Link.lrLoopA_atoms nt bits)
    rw [Res.loop_calls, hnI] at hci
    have hi : i = (calls es1).length := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · rw [List.getElem?_append_left hlt] at hci
        have hc1 := walk_callees (σ := σI) (loopBody fn) (c := c) (by rw [hw1]; exact List.mem_of_getElem? hci)
        rw [hlb] at hc1
        cases hc1
      · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by simp; omega)] at hci
        cases hci
    subst hi
    rw [List.getElem?_append_right le_rfl, Nat.sub_self] at hci
    simp only [List.getElem?_singleton, ↓reduceIte, Option.some.injEq] at hci
    subst hci
    obtain ⟨j, hj⟩ := B2C.idxOf_of_find hfI
    obtain ⟨i2, hji2, hi2, -, hf', hc', -⟩ := fn_of_idx hj
    have hcj : coreOf j = fn := by rw [hc']; exact Option.some.inj (hf'.symm.trans hfI)
    have hH := B2C.H_eq_kidHdr hIt hj (by rw [hcj]; exact hw) (calls es1).length
    unfold kidHdr at hH
    rw [Res.loop_calls, hnI, List.getElem?_append_right le_rfl, Nat.sub_self] at hH
    simp only [List.getElem?_singleton, ↓reduceIte] at hH
    rw [ite_eq_left (show (coreOf j).loop = true ∧ _ from ⟨by rw [hcj]; exact hl', by simp⟩)] at hH
    rw [hparL] at hps
    obtain ⟨rfl, rfl⟩ := List.cons.inj hps
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
    obtain ⟨hp0, hp1, hp2, -, -⟩ := hpar
    obtain ⟨a, jj, h, n, hh2, h10, hm10, hn64, hhn, hq0, hjh, hn1, hrec⟩ := hQI fI σI bufsI kidsI hIt nt bits main hmem
    have hne : σI c0 ≠ 0 := by simpa using hct
    rw [hc0, hq0] at hne
    simp only [Res.endVal, hparL, hn1] at hne
    have hj1 : jj + 1 ≠ h := by
      rintro rfl
      apply hne
      rw [← gen_pow_eq_ofK, ← pow_add, CharTwo.add_self_eq_zero]
    have h18 : σI (.n 18) = refMem r.img (a + 7) * gen ^ (4 * lrW nt bits * jj) := by
      rw [h9, hq0, ← pow_mul, mul_comm jj 7] at l5
      exact B1.loadHolds_unique l5 hrec
    refine ⟨a, jj + 1, h, n, by rw [hhdr, hH, hh2], h10, hm10, hn64, hhn, by rw [hp0, hi0, hq0, ← gen_pow_eq_ofK,
      ← pow_add], by omega, by rw [hp1, hn1], ?_⟩
    rw [hp2, B1.loadHolds_mul_gen_pow]
    rw [h9, hq0, ← pow_mul, B1.loadHolds_mul_gen_pow, h18, mul_assoc, ← pow_add] at l12
    rw [show 7 * (jj + 1) + 5 = jj * 7 + 12 by ring, show 4 * lrW nt bits * (jj + 1) =
      4 * lrW nt bits * jj + 4 * lrW nt bits by ring]
    exact l12

/-- **`LrQ` at every honest instance.** -/
theorem lrQ_allA (hR : RefH (layB al) (D r) r) (hr : r.Ok) : ∀ J ∈ instsR al D r, LrQ r J := by
  refine insts_allA hR (lrQ_stepA hR hr) fun J hm ↦ ?_
  intro f σ bufs kids hJt nt bits main hmem
  have hn := hm _ _ _ _ hJt
  subst hn
  exact absurd rfl (lrSpecs_not_main _ hmem)

/-- **A loop of `link_rounds` is a cursor-run loop** (`StLoopOkA`): its cursor, the record's, lies `4Wj` words past
`cursor` (the caller's cell `7`), with `4W` words of room below `W·n`, `g^n` the caller's cell `10`. -/
theorem lr_stOk {nt bits : ℕ} {main loop : String} (hmem : (nt, bits, main, loop) ∈ lrSpecs) {W S : ℕ}
    (hWd : lrW nt bits = W) (hS : S = 4 * W) : StLoopOkA al D (loop, 7, 10, W, 18, S) := by
  subst hWd hS
  refine ⟨by dsimp only; decide, by dsimp only; decide, by dsimp only; unfold CoreMode.GB; decide, ?_, ?_⟩
  · have : 0 < lrW nt bits := by unfold lrW; omega
    dsimp only
    omega
  intro r hR hr I hI σ bufs kids ht fn hf
  dsimp only
  obtain ⟨a, j, h, n, hh2, h10, hm10, hn64, hhn, hq0, hjh, hn1, hrec⟩ := lrQ_allA hR hr I hI loop σ bufs kids ht
    nt bits main hmem
  obtain ⟨hW, ⟨fL, hfL, -, -, -, hbodyL⟩, -⟩ := lrSpec_all hmem
  obtain rfl : fn = fL := Option.some.inj (hf.symm.trans hfL)
  obtain ⟨args, rets, fn', hf', -, es, vs, hw, -, hh, -⟩ := inst_validA hR hI ht
  obtain rfl : fn' = fn := Option.some.inj (hf'.symm.trans hf)
  obtain ⟨h9, l5, -⟩ := lrIter hW (lrLoop_atoms hbodyL hw hh)
  rw [h9, hq0, ← pow_mul, mul_comm j 7] at l5
  refine ⟨a, 4 * j, n, hh2, by omega, h10, ?_, hm10, by unfold CoreMode.capE; omega, ?_⟩
  · rw [B1.loadHolds_unique l5 hrec]
    congr 2
    ring
  · have : lrW nt bits * (4 * j) + 4 * lrW nt bits = lrW nt bits * (4 * (j + 1)) := by ring
    rw [this]
    exact Nat.mul_le_mul_left _ (by omega)

end

end LeanVM.Guest.EndExec
