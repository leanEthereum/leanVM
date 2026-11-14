/-
  LeanVM.Guest.EndExecACur

  The cursor follows each step of the tree track: `CurArith` on the deployed alignment, from the step
  rule's offsets (`Bridge.stepRule_off`) and the bump pointer check (`Bridge.curJ_all`).
-/

module

public import LeanVM.Guest.EndExecAKeep
public import LeanVM.Guest.EndExecJumpCells
public import LeanVM.Guest.Bridge.StepOff
public import LeanVM.Guest.Bridge.AllocCur
public import LeanVM.Guest.Bridge.AllocChk.All
public import LeanVM.Guest.Bridge.JumpCells.All

/-!
# The cursor along the run

`curArith_alignA : CurArith alignA`. A step from a state of the tree track is one of `StepOff`'s
kinds; in each the top frame's cursor moves by the words the hints at its offset reserve
(`treeSizes`, summed by `treeSizes_sum`), from what the bump pointer check gives at the offsets
(`Bridge.AllocCur`):

* within the frame (`fall`, `fwd`, `skip`): the buffer hints counted past the offset, a frame hint
  pending past it, or consumed by a call not taken (a phantom's words are its block);
* a call (`push`): the callee at the cursor past every buffer and the earlier callees, its frame the
  block the pending frame hint reserved (`Memory.kid_pos`), its subtree ending where the caller
  resumes at the site's return pc (`Memory.endCur_kid`);
* a loop's tail call (`tail`): the next iteration at the cursor past everything (`Memory.tail_pos`),
  ending where the iteration does (`Memory.endCur_tail`);
* a return (`ret`): the frame ends at its cursor past everything (`Memory.endCur_ret`, a loop's last
  callee a phantom by `TailA`), where the frame below resumes (`ChainA`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Guest.Check (getF)
open LeanVM.Prover.Exec

@[expose] public section

/-- Sizes of hints in order: those of `p` the next values of `g` from `n`, those of `q` `B`, the
others nothing. -/
def tsz {α : Type} (p q : α → Bool) (g : ℕ → ℕ) (B : ℕ) (hs : List α) (n : ℕ) : List ℕ :=
  (List.range hs.length).map fun i ↦ match hs[i]? with
    | some h => if p h then g (n + ((hs.take i).filter p).length) else if q h then B else 0
    | none => 0

end

public section

/-! ## The words the hints at an offset reserve -/

theorem tsz_cons {α : Type} (p q : α → Bool) (g : ℕ → ℕ) (B : ℕ) (a : α) (hs : List α) (n : ℕ) :
    tsz p q g B (a :: hs) n =
      (if p a then g n else if q a then B else 0) :: tsz p q g B hs (n + if p a then 1 else 0) := by
  unfold tsz
  rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
  refine congrArg₂ List.cons (by simp) (List.map_congr_left fun i _ ↦ ?_)
  simp only [Function.comp, List.getElem?_cons_succ, List.take_succ_cons, List.filter_cons]
  cases hs[i]? with
  | none => rfl
  | some h =>
    by_cases ha : p a = true
    · simp only [ha, ↓reduceIte, List.length_cons]
      congr 2; omega
    · simp [ha]

theorem tsz_sum {α : Type} (p q : α → Bool) (g : ℕ → ℕ) (B : ℕ) :
    ∀ (hs : List α) (n : ℕ), (tsz p q g B hs n).sum =
      ((List.range (hs.countP p)).map fun k ↦ g (n + k)).sum + hs.countP (fun h ↦ !p h && q h) * B
  | [], n => by simp [tsz]
  | a :: hs, n => by
    rw [tsz_cons, List.sum_cons, tsz_sum p q g B hs, List.countP_cons, List.countP_cons]
    by_cases ha : p a = true
    · simp only [ha, ↓reduceIte, Bool.not_true, Bool.false_and, Bool.false_eq_true, Nat.add_zero]
      rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
      have : ((List.range (hs.countP p)).map ((fun k ↦ g (n + k)) ∘ Nat.succ)) =
          (List.range (hs.countP p)).map fun k ↦ g (n + 1 + k) := by
        apply List.map_congr_left; intro k _; simp only [Function.comp]; congr 1; omega
      rw [this, Nat.add_zero]
      simp only [Nat.add_zero]
      omega
    · simp only [ha, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Bool.not_false, Bool.true_and]
      cases hq : q a
      · simp
      · simp only [↓reduceIte, Nat.add_mul, Nat.one_mul]
        omega

theorem take_sum_range (bufs : List ℕ) (n : ℕ) :
    ∀ m, (bufs.take n).sum + ((List.range m).map fun k ↦ bufs.getD (n + k) 0).sum = (bufs.take (n + m)).sum
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, ← Nat.add_assoc, take_sum_range bufs n m,
      show n + (m + 1) = n + m + 1 by omega, List.take_add_one, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [List.getD_eq_getElem?_getD]
    cases bufs[n + m]? <;> simp

theorem take_sum_le {bufs : List ℕ} {n : ℕ} (h : bufs.length ≤ n) : (bufs.take n).sum = bufs.sum := by
  rw [List.take_of_length_le h]

theorem isFrame_notBuf {X : AlignCtx} {h : Prover.Exec.Hint} (hf : isFrame X h = true) : isBuf X h = false := by
  unfold isBuf; simp [hf]

/-- **The words the hints at an offset reserve**: the next buffers past the ones before it, and the
next callee's block for each frame hint. -/
theorem treeSizes_sum (A : String → FnAl) (e : Ent) (off : ℕ) :
    (e.I.t.bufs.take (nbAt (A e.I.t.name).X (A e.I.t.name).d off)).sum + (treeSizes A e off).sum =
      (e.I.t.bufs.take (nbAt (A e.I.t.name).X (A e.I.t.name).d off +
        (hintsAtOff (A e.I.t.name) off).countP (isBuf (A e.I.t.name).X))).sum +
      (hintsAtOff (A e.I.t.name) off).countP (isFrame (A e.I.t.name).X) *
        (((e.I.t.kidsC coreProgram.loop)[e.nc]?).map (Tree.block B2C.fs coreProgram.loop)).getD 0 := by
  have h1 : treeSizes A e off = tsz (isBuf (A e.I.t.name).X) (isFrame (A e.I.t.name).X) (fun k ↦ e.I.t.bufs.getD k 0)
      ((((e.I.t.kidsC coreProgram.loop)[e.nc]?).map (Tree.block B2C.fs coreProgram.loop)).getD 0)
      (hintsAtOff (A e.I.t.name) off) (nbAt (A e.I.t.name).X (A e.I.t.name).d off) := by
    simp only [treeSizes, tsz]
    refine List.map_congr_left fun i _ ↦ ?_
    cases (hintsAtOff (A e.I.t.name) off)[i]? <;> rfl
  rw [h1, tsz_sum, ← Nat.add_assoc, take_sum_range]
  congr 2
  apply List.countP_congr
  intro h _
  cases hf : isFrame (A e.I.t.name).X h
  · simp
  · simp [isFrame_notBuf hf]

/-! ## What the bump pointer check gives -/

theorem frameOk_spec {X : AlignCtx} {code : List OffsetInstruction} {a : ℕ} {h : Prover.Exec.Hint}
    (hf : frameOk X code a h = true) :
    ∃ oc od q, code[nextJump code a]? = some (.jump oc od q) ∧ allocPtr h = some q ∧ X.zeroAt oc = false ∧
      X.selfAt q = false ∧ X.nextAt q = false ∧ ¬(od = 0 ∧ q = 1) := by
  unfold frameOk at hf
  rw [Bool.and_eq_true] at hf
  obtain ⟨-, h2⟩ := hf
  split at h2
  · rename_i oc od q p hc hp
    simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq] at h2
    obtain ⟨⟨⟨⟨rfl, h3⟩, h4⟩, h5⟩, h6⟩ := h2
    refine ⟨oc, od, q, hc, hp, h3, h4, h5, fun ⟨h0, h1⟩ ↦ ?_⟩
    subst h0 h1
    simp at h6
  · cases h2

/-- **What the bump pointer check gives** of a function's code and body. -/
structure CurFacts (X : AlignCtx) (P : B2C.Plumb) (body : List Stmt) (code : List OffsetInstruction)
    (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : Prop where
  bufs : ∀ (i oc od of : ℕ), code[i]? = some (.jump oc od of) →
    (∀ q ∈ bufsOf X d, q.1 ≤ i) ∨ bufJumpOk X (bufsOf X d) i oc od of = true
  frame : ∀ q ∈ frames X d, frameOk X code q.1 q.2 = true
  uniq : FrUniq code (frames X d)
  site : P.sites ≠ [] → ∀ (i oc od of : ℕ), code[i]? = some (.jump oc od of) → (getF X.sites of).isSome = true →
    ∃ r ∈ frames X d, allocPtr r.2 = some of ∧ nextJump code r.1 = i
  tgt : ∀ (i oc od of : ℕ), code[i]? = some (.jump oc od of) → ∀ t, X.pcAt od = some t →
    pendIn code (frames X d) (t - X.entry) = false
  arm : ∀ s ∈ stmtsOf body, ∀ x arms, s = .match_ x arms → ∀ od a k t, (od, a) ∈ armsOf P → a.1 = x.idx →
    k < arms.length → getF X.jt (a.2 + k) = some t → pendIn code (frames X d) (t - X.entry) = false
  ret : ∀ s ∈ P.sites, pendIn code (frames X d) (s.r - X.entry) = false
  cnt : cntL body ≤ (bufsOf X d).length

theorem pendIn_nil (code : List OffsetInstruction) (off : ℕ) : pendIn code [] off = false := rfl

theorem curFacts_of {X : AlignCtx} {P : B2C.Plumb} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (h : curChk X P body code d = true) : CurFacts X P body code d := by
  simp only [curChk, curCode, curBody, Exec.listSeq_eq, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨hj, -⟩, -⟩, hfr⟩, hso⟩, hret⟩, hcnt, harm⟩ := h
  have hfr' : ∀ q ∈ frames X d, frameOk X code q.1 q.2 = true := hfr
  have hnil : frames X d = [] → ∀ off, pendIn code (frames X d) off = false := fun h0 off ↦ by rw [h0]; rfl
  refine ⟨fun i oc od of hi ↦ ?_, hfr', fun i ins hi hjj ↦ ?_, fun hs i oc od of hi hsi ↦ ?_, fun i oc od of hi t ht ↦ ?_,
    fun s hs x arms he od a k t ha hax hk ht ↦ ?_, hret, hcnt⟩
  · have := bufsJumps_at 0 code hj i oc od of hi
    rwa [Nat.zero_add] at this
  · rcases hso with ⟨h0, -⟩ | ⟨hs, -⟩
    · simp only [List.isEmpty_iff] at h0
      have h0' : frames X d = [] := h0
      rw [h0']; simp
    · cases ins with
      | jump oc od of =>
        have := (sitesOk_at 0 code hs i oc od of hi).2
        rwa [Nat.zero_add] at this
      | _ => cases hjj
  · rcases hso with ⟨-, h0⟩ | ⟨hs', -⟩
    · simp only [List.isEmpty_iff] at h0; exact absurd h0 hs
    · have := (sitesOk_at 0 code hs' i oc od of hi).1 hsi
      rwa [Nat.zero_add] at this
  · rcases hso with ⟨h0, -⟩ | ⟨-, ht'⟩
    · simp only [List.isEmpty_iff] at h0; exact hnil h0 _
    · exact targetsOk_at code ht' i oc od of hi t ht
  · rcases harm with h0 | hb
    · simp only [List.isEmpty_iff] at h0; exact hnil h0 _
    · exact armTgtsOk_at (blockM_sels _ body hb s hs x arms he) ha hax hk ht

/-- **A jump through the own frame, on a constant `0`, through a next frame or a return** is no frame
hint's. -/
theorem noFrame_of {X : AlignCtx} {P : B2C.Plumb} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hF : CurFacts X P body code d) {off oc od of : ℕ}
    (hi : code[off]? = some (.jump oc od of))
    (hk : X.zeroAt oc = true ∨ X.selfAt of = true ∨ X.nextAt of = true ∨ (od = 0 ∧ of = 1)) :
    ∀ q ∈ frames X d, nextJump code q.1 ≠ off := fun q hq he ↦ by
  obtain ⟨oc', od', q', hc, -, h1, h2, h3, h4⟩ := frameOk_spec (hF.frame q hq)
  rw [he, hi] at hc
  cases hc
  rcases hk with h | h | h | h
  · rw [h] at h1; cases h1
  · rw [h] at h2; cases h2
  · rw [h] at h3; cases h3
  · exact h4 h

theorem frJump_of {X : AlignCtx} {P : B2C.Plumb} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hF : CurFacts X P body code d) : FrJump code (frames X d) :=
  fun q hq ↦ let ⟨_, _, _, hc, _⟩ := frameOk_spec (hF.frame q hq); ⟨_, hc⟩

/-! ## The cursor and the chain by frame -/

theorem cursorAt_congr {A : String → FnAl} {e e' : Ent} (hI : e'.I = e.I) (hnc : e'.nc = e.nc) :
    cursorAt A e' = cursorAt A e := by
  funext off; unfold cursorAt; rw [hI, hnc]

theorem tailA_congr {e e' : Ent} (hI : e'.I = e.I) (hnc : e'.nc = e.nc) (h : TailA e) : TailA e' := by
  unfold TailA at *; rw [hI, hnc]; exact h

/-- The chain with a new top frame of the same instance, `TailA`. -/
theorem chainA_top {A : String → FnAl} {M : ℕ → E} {e e' : Ent} {st : List Ent} (hI : e'.I = e.I)
    (ht : TailA e') (h : ChainA A M (e :: st)) : ChainA A M (e' :: st) := by
  cases st with
  | nil => exact ht
  | cons e2 st2 => exact ⟨ht, hI ▸ h.2.1, h.2.2⟩

theorem chainA_tail {A : String → FnAl} {M : ℕ → E} {e : Ent} {st : List Ent} (h : ChainA A M (e :: st)) :
    TailA e := by
  cases st with
  | nil => exact h
  | cons _ _ => exact h.1

theorem chainA_rest {A : String → FnAl} {M : ℕ → E} {e e2 : Ent} {st : List Ent} (h : ChainA A M (e :: e2 :: st)) :
    ChainA A M (e2 :: st) := h.2.2

theorem tailA_enter {P : Core.Program} (J : Inst) (fn : Fn) : TailA (Ent.enter P J fn) :=
  fun _ hl hk ↦ absurd (List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)) hk

theorem nbAt_zero (X : AlignCtx) (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : nbAt X d 0 = 0 := by
  unfold nbAt; simp

theorem pendAt_zero (X : AlignCtx) (code : List OffsetInstruction) (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) :
    pendAt X code d 0 = false := by
  unfold pendAt pendIn; simp

/-- **A callee's cursor at its entry** is its instance's. -/
theorem cursorAt_enter (A : String → FnAl) {P : Core.Program} (J : Inst) (fn : Fn) :
    cursorAt A (Ent.enter P J fn) 0 = J.cur := by
  unfold cursorAt
  simp only [Ent.enter, nbAt_zero, pendAt_zero, Inst.curAt, Ent.nc, calls]
  simp

/-- **The cursor moved by the hints at an offset.** -/
theorem cursor_step (A : String → FnAl) (e : Ent) (off : ℕ) :
    cursorAt A e off + (treeSizes A e off).sum =
      e.I.cur + (e.I.t.bufs.take (nbAt (A e.I.t.name).X (A e.I.t.name).d off +
        (hintsAtOff (A e.I.t.name) off).countP (isBuf (A e.I.t.name).X))).sum +
      (((e.I.t.kidsC coreProgram.loop).take e.nc).map (Tree.total B2C.fs)).sum +
      ((bif pendAt (A e.I.t.name).X (A e.I.t.name).code (A e.I.t.name).d off then 1 else 0) +
        (hintsAtOff (A e.I.t.name) off).countP (isFrame (A e.I.t.name).X)) *
        (((e.I.t.kidsC coreProgram.loop)[e.nc]?).map (Tree.block B2C.fs coreProgram.loop)).getD 0 := by
  have h := treeSizes_sum A e off
  unfold cursorAt Inst.curAt
  cases pendAt (A e.I.t.name).X (A e.I.t.name).code (A e.I.t.name).d off <;> simp only [Bool.cond_true, Bool.cond_false] <;>
    rw [Nat.add_mul] <;> omega

theorem kidsValid_len {P : Core.Program} {rd : Reader} {σ : Val} :
    ∀ {cs : List Call} {ks : List Tree}, Tree.KidsValid P rd σ cs ks → cs.length = ks.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp only [List.length_cons, kidsValid_len h.2.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem nextAt_selfAt {X : AlignCtx} {o : ℕ} (h : X.nextAt o = true) : X.selfAt o = false := by
  unfold AlignCtx.nextAt at h
  unfold AlignCtx.selfAt
  split at h
  · rename_i S hS
    rw [hS]
    cases S with
    | zero => simp at h
    | succ S => rfl
  · cases h

theorem take_map_sum_le {l : List Tree} {n : ℕ} (h : l.length ≤ n) :
    ((l.take n).map (Tree.total B2C.fs)).sum = (l.map (Tree.total B2C.fs)).sum := by
  rw [List.take_of_length_le h]

/-! ## A frame of the deployed guest -/

section Frame

variable {r : Ref}

/-- What the bump pointer check gives of a frame's function. -/
theorem curFacts_frame {f : String} {j : ℕ} (hj : B2C.idxOf f = some j) :
    CurFacts (alignA f).X (B2C.plumbOf j) (alignA f).body (alignA f).code (alignA f).d := by
  obtain ⟨i, rfl, -, -, -, -, -, -, h1, h2⟩ := B2C.fn_of_idx hj
  rw [alignA_of hj]
  exact curFacts_of (AllocChk.curJ_all _ h1 (by have : nFns = 1602 := rfl; omega))

/-- A frame's function's advice by increasing pcs from its entry. -/
theorem hintsUp_frame {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn) :
    HintsUp (alignA f).d (alignA f).X.entry := by
  have hok := progAl.ok _ _ hf
  rw [alignOk, AlignCtx.seq_eq] at hok
  simp only [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, Nat.ble_eq] at hok
  exact ⟨hok.1.1.1.2, hok.1.1.2, hok.1.2⟩

/-- **A jump through a next frame is a loop helper's.** -/
theorem loop_of_nextAt {f : String} {j : ℕ} (hj : B2C.idxOf f = some j) {off oc od of : ℕ}
    (hcode : (alignA f).code[off]? = some (.jump oc od of)) (hnx : (alignA f).X.nextAt of = true) :
    coreProgram.loop f = true := by
  obtain ⟨i0, rfl, hi0, -, hfind, hcore, -, -, h1, h2⟩ := B2C.fn_of_idx hj
  rw [Program.loop_of_find? hfind, ← hcore]
  have hd := JumpCells.jcData_all _ h1 (by have : nFns = 1602 := rfl; omega)
  unfold jcData jcDataD at hd
  simp only [Bool.and_eq_true] at hd
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hnext⟩ := hd
  rw [alignA_of hj] at hcode hnx
  unfold AlignCtx.nextAt at hnx
  split at hnx
  · rename_i S hso
    have hm := statOf_ofData hso
    have hS : S ≠ 0 := fun h0 ↦ by simp [h0] at hnx
    rcases Bool.or_eq_true _ _ |>.mp hnext with hn | hn
    · have := List.all_eq_true.mp hn _ hm
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at this
      rcases this with h0 | h0
      · exact absurd h0 hS
      · exact h0.1
    · have hmem : OffsetInstruction.jump oc od of ∈ (fnOf (i0 + 1)).code := List.mem_of_getElem? hcode
      have := List.all_eq_true.mp (List.all_eq_true.mp hn _ hmem) _ hm
      simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq,
        Bool.and_eq_true] at this
      rcases this with h0 | h0
      · exact absurd h0 hS
      · exact h0.1
  · cases hnx

/-- **A loop helper's call through a call site is not its last.** -/
theorem notLast_of_site {f : String} {j : ℕ} (hj : B2C.idxOf f = some j) {σ : Val} {es : List Ev} {vs : List V}
    (hw : walk σ (coreOf j).body = .ret es vs) (hl : coreProgram.loop f = true) {i : ℕ} {c : Call}
    (hc : (calls es)[i]? = some c) {q : ℕ} {s : B2C.Site} (hs : (alignA f).X.siteAt q c.args c.rets = some s) :
    i + 1 < (calls es).length := by
  obtain ⟨i0, rfl, hi0, -, hfind, hcore, -, -, h1, h2⟩ := B2C.fn_of_idx hj
  have hd := JumpCells.jcData_all _ h1 (by have : nFns = 1602 := rfl; omega)
  unfold jcData jcDataD at hd
  simp only [Bool.and_eq_true] at hd
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, hloop⟩, -⟩ := hd
  have hl' : (coreOf (i0 + 1)).loop = true := by rw [hcore, ← Program.loop_of_find? hfind]; exact hl
  simp only [hl', Bool.not_true, Bool.false_or, Bool.and_eq_true] at hloop
  rw [alignA_of hj] at hs
  obtain ⟨hsm, -, hsa, hsr⟩ := siteAt_ofData hs
  have hlt := (List.getElem?_eq_some_iff.mp hc).1
  by_contra hge
  exact loop_last hloop.2 hw hc (by omega) s hsm ⟨hsa, hsr⟩

/-- **A callee instance at its position** in the caller's `kidPos`. -/
theorem kid_place (hr : r.Ok) {I J : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    (hJ : J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) {i : ℕ} (hk : I.t.kids[i]? = some J.t)
    (hkf : I.kidFps[i]? = some J.fp) :
    (kidPos B2C.fs coreProgram.loop (I.fp, I.cur) I.t.name I.t.bufs
      (I.t.kids.map (Tree.sz B2C.fs coreProgram.loop)))[i]? = some (J.fp, J.cur) := by
  obtain ⟨rd, hHon, -⟩ := hr.honest
  have hI' : I ∈ r.T.insts B2C.fs coreProgram.loop B2C.H (0, r.T.block B2C.fs coreProgram.loop) r.hdr := hI
  have hJ' : J ∈ r.T.insts B2C.fs coreProgram.loop B2C.H (0, r.T.block B2C.fs coreProgram.loop) r.hdr := hJ
  obtain ⟨J', hJ'm, hJt, hpos⟩ := insts_kid_pos r.T _ r.hdr I hI' i J.t hk
  have hIP := insts_placed r.T (0, r.T.block B2C.fs coreProgram.loop) r.hdr (by omega) I hI'
  have hfp : J'.fp = J.fp := by
    rw [hIP.1, List.getElem?_map, hpos] at hkf
    exact Option.some.inj hkf
  have hpw := insts_pairwise (fs := B2C.fs) (lp := coreProgram.loop) (H := B2C.H) r.T (0, r.T.block B2C.fs coreProgram.loop) r.hdr (by omega)
  have hJJ : J' = J := inst_eq_of_fp hpw hJ'm hJ' hfp (by have := hHon.cells.two_le J' hJ'm; omega)
    (by have := hHon.cells.two_le J hJ; omega)
  rw [hpos, hJJ]

/-- **A frame's buffers are at most its function's buffer hints.** -/
theorem bufs_le (hr : r.Ok) {pc fp : ℕ} {done : List Pop} {st : List Ent} (htr : RefTrack alignA r pc fp (done, st))
    {e : Ent} (he : e ∈ st) : e.I.t.bufs.length ≤ (bufsOf (alignA e.I.t.name).X (alignA e.I.t.name).d).length := by
  obtain ⟨rd, hHon, hHX⟩ := hr.honest
  obtain ⟨hI, j, bufs, kids, vs, hj, hIt, hfn, hw, -⟩ := (htr.frames hr.name hHon hHX.covers) e he
  have hE := htr.track.ents e he
  obtain ⟨t, ν, hv, -, hpl, -, -, -, hTt⟩ := hr.tree
  have hTp : r.T.Placed coreProgram B2C.fs B2C.cert (0, r.T.block B2C.fs coreProgram.loop) := by
    rw [hTt, block_retemp]
    exact placed_retemp coreProgram_fresh t _ hv hpl
  have hI' : e.I ∈ r.T.insts B2C.fs coreProgram.loop B2C.H (0, r.T.block B2C.fs coreProgram.loop) r.hdr := hI
  have hIp := insts_placedAt r.T _ r.hdr hTp e.I hI'
  have hIP := insts_placed r.T (0, r.T.block B2C.fs coreProgram.loop) r.hdr (by omega) e.I hI'
  have hn := (Inst.nodeAt hIp hIP hIt).1
  have hlen := congrArg List.length hn
  rw [List.length_map, List.length_map, hIP.2.1, length_bases] at hlen
  have hevs : e.I.t.events coreProgram = e.pre ++ e.es := by rw [hIt]; exact events_node hE.find hw
  rw [hevs] at hlen
  have hc := allocDsts_le_cnt hw
  have hF := (curFacts_frame hj).cnt
  rw [alignA_of hj] at hF ⊢
  change cntL (coreOf j).body ≤ _ at hF
  rw [hfn] at hF
  omega

end Frame

theorem siteAt_some {X : AlignCtx} {q : ℕ} {args rets : List V} {s : B2C.Site} (h : X.siteAt q args rets = some s) :
    (getF X.sites q).isSome = true := by
  unfold AlignCtx.siteAt at h
  split at h
  · rename_i s' hs'; rw [hs']; rfl
  · cases h

theorem phantom_last {fs : String → ℕ} {lp : String → Bool} {kids : List Tree} {nc : ℕ} {f : String} {σ' : Val}
    (hk : kids[nc]? = some (.phantom f σ')) (hl : kids.length = nc + 1) (hne : kids ≠ []) :
    (kids.getLast hne).total fs = (kids.getLast hne).block fs lp := by
  rw [List.getLast_eq_getElem]
  have : kids[kids.length - 1]'(by omega) = .phantom f σ' := by
    rw [List.getElem?_eq_some_iff] at hk
    obtain ⟨_, hk⟩ := hk
    simp only [hl, Nat.add_sub_cancel]; exact hk
  rw [this]; simp [Tree.total, Tree.block]

/-! ## The step -/

theorem cursorAt_unfold (A : String → FnAl) (e : Ent) (off : ℕ) :
    cursorAt A e off = e.I.cur + (e.I.t.bufs.take (nbAt (A e.I.t.name).X (A e.I.t.name).d off)).sum +
      (((e.I.t.kidsC coreProgram.loop).take e.nc).map (Tree.total B2C.fs)).sum +
      (bif pendAt (A e.I.t.name).X (A e.I.t.name).code (A e.I.t.name).d off then 1 else 0) *
        (((e.I.t.kidsC coreProgram.loop)[e.nc]?).map (Tree.block B2C.fs coreProgram.loop)).getD 0 := by
  unfold cursorAt Inst.curAt
  cases pendAt (A e.I.t.name).X (A e.I.t.name).code (A e.I.t.name).d off <;> simp

theorem kidsC_length {lp : String → Bool} (t : Tree) :
    (t.kidsC lp).length = if lp t.name then t.kids.length - 1 else t.kids.length := by
  unfold Tree.kidsC; split <;> simp

theorem ksum_succ {fs : String → ℕ} {lp : String → Bool} {t : Tree} {nc : ℕ} (h : nc < (t.kidsC lp).length) :
    (((t.kidsC lp).take (nc + 1)).map (Tree.total fs)).sum =
      (((t.kidsC lp).take nc).map (Tree.total fs)).sum + ((t.kidsC lp)[nc]).total fs := by
  simp only [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

theorem kidsC_getElem? {lp : String → Bool} {t : Tree} {nc : ℕ} (h : nc < (t.kidsC lp).length) :
    (t.kidsC lp)[nc]? = t.kids[nc]? := by
  rw [List.getElem?_eq_getElem h, kidsC_getElem h, List.getElem?_eq_getElem]

theorem bif01 (b : Bool) : (bif b then 1 else 0) = if b = true then 1 else 0 := by cases b <;> rfl

/-- **The cursor follows each step of the tree track**, on the deployed alignment. -/
theorem curArith_alignA : CurArith alignA := by
  intro r hr pc fp done e st r' htr hch hstep hne'
  obtain ⟨rd, hHon, hHX⟩ := hr.honest
  obtain ⟨hI, j, bufs, kids, vs, hj, hIt, hfn, hw, -⟩ := (htr.frames hr.name hHon hHX.covers) e List.mem_cons_self
  have hE := htr.track.ents e List.mem_cons_self
  have hF := curFacts_frame hj
  have hU := hintsUp_frame hE.find
  have hbl := bufs_le hr htr List.mem_cons_self
  have hkl : (calls (e.pre ++ e.es)).length = e.I.t.kids.length := by
    obtain ⟨rv, hkv⟩ := hE.kids; exact kidsValid_len hkv
  have hnode : ∃ f σ bufs kids, e.I.t = .node f σ bufs kids := ⟨_, _, _, _, hIt⟩
  have hwj : walk e.σ (coreOf j).body = .ret (e.pre ++ e.es) vs := by rw [hfn]; exact hw
  obtain ⟨off, hpc, pc', fp', ⟨done', st'⟩, hr', hts', hk⟩ :=
    stepRule_off progAl honest_closed htr (jumpCells_at r hr _ _ _ _ _ htr) hstep hne'
  have hoff : pc - entOf alignA e.I.t.name = off := by omega
  rw [hoff]
  have hstep' := cursor_step alignA e off
  have hfrAt : (hintsAtOff (alignA e.I.t.name) off).countP (isFrame (alignA e.I.t.name).X) =
      (frames (alignA e.I.t.name).X (alignA e.I.t.name).d).countP (fun q ↦ decide (q.1 = off)) :=
    (countP_at hU (fun _ ↦ isFrame_ptr (X := (alignA e.I.t.name).X)) off).symm
  have hpd : ∀ o, pendAt (alignA e.I.t.name).X (alignA e.I.t.name).code (alignA e.I.t.name).d o =
      pendIn (alignA e.I.t.name).code (frames (alignA e.I.t.name).X (alignA e.I.t.name).d) o := fun _ ↦ rfl
  have hnbS := nb_succ (X := (alignA e.I.t.name).X) hU off
  -- all the buffer hints at or before a jump that is no forward jump in the frame
  have hnone : ∀ oc od of, (alignA e.I.t.name).code[off]? = some (.jump oc od of) →
      bufJumpOk (alignA e.I.t.name).X (bufsOf (alignA e.I.t.name).X (alignA e.I.t.name).d) off oc od of = false →
      nbAt (alignA e.I.t.name).X (alignA e.I.t.name).d off +
          (hintsAtOff (alignA e.I.t.name) off).countP (isBuf (alignA e.I.t.name).X) =
        (bufsOf (alignA e.I.t.name).X (alignA e.I.t.name).d).length ∧
      ∀ t, off < t → nbAt (alignA e.I.t.name).X (alignA e.I.t.name).d t =
        (bufsOf (alignA e.I.t.name).X (alignA e.I.t.name).d).length := fun oc od of hi hb ↦ by
    rcases hF.bufs off oc od of hi with h | h
    · exact nb_none hU h
    · rw [h] at hb; cases hb
  have hkC := kidsC_length (lp := coreProgram.loop) e.I.t
  cases hk with
  | @fall e' ins hI' hnc' hins hjk =>
    refine ⟨_, _, done', _, st, hr', hts', ?_, chainA_top hI' (tailA_congr hI' hnc' (chainA_tail hch)) hch⟩
    rw [cursorAt_congr hI' hnc', hI', show entOf alignA e.I.t.name + off + 1 - entOf alignA e.I.t.name = off + 1 by omega,
      hstep', cursorAt_unfold, hnbS]
    have hpe : (bif pendAt (alignA e.I.t.name).X (alignA e.I.t.name).code (alignA e.I.t.name).d (off + 1) then 1 else 0) =
        (bif pendAt (alignA e.I.t.name).X (alignA e.I.t.name).code (alignA e.I.t.name).d off then 1 else 0) +
          (hintsAtOff (alignA e.I.t.name) off).countP (isFrame (alignA e.I.t.name).X) := by
      cases ins with
      | jump oc od of =>
        have hn := noFrame_of hF hins (by rcases hjk oc od of rfl with h | h <;> simp [h])
        obtain ⟨h1, h2, h3⟩ := pend_nf hins rfl hn
        rw [hfrAt, h2, hpd, hpd, h1, h3]
        rfl
      | _ =>
        rw [hfrAt, hpd, hpd, pend_succ (frJump_of hF) hF.uniq hins rfl]
    rw [hpe]
    rfl
  | @fwd e' oc od of _ hI' hnc' hins hz0 hself htgt hlt =>
    refine ⟨_, _, done', _, st, hr', hts', ?_, chainA_top hI' (tailA_congr hI' hnc' (chainA_tail hch)) hch⟩
    rw [cursorAt_congr hI' hnc', hI', hstep', cursorAt_unfold]
    have hlt' : off < pc' - entOf alignA e.I.t.name := by omega
    obtain ⟨h1, h2, -⟩ := pend_nf hins rfl (noFrame_of hF hins (Or.inr (Or.inl hself)))
    have hnb : nbAt (alignA e.I.t.name).X (alignA e.I.t.name).d (pc' - entOf alignA e.I.t.name) =
        nbAt (alignA e.I.t.name).X (alignA e.I.t.name).d off +
          (hintsAtOff (alignA e.I.t.name) off).countP (isBuf (alignA e.I.t.name).X) := by
      rcases hF.bufs off oc od of hins with h | h
      · obtain ⟨ha, hb⟩ := nb_none hU h
        rw [hb _ hlt']; exact ha.symm
      · unfold bufJumpOk at h
        simp only [hz0, Bool.false_or, Bool.and_eq_true] at h
        obtain ⟨⟨⟨⟨-, -⟩, -⟩, harm⟩, hpc'⟩ := h
        rcases htgt with ht | ⟨z, x, arms, ss, a, k, hz, hzc, ha, hax, hk, hjt⟩
        · rw [ht] at hpc'
          simp only [List.all_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt] at hpc'
          refine nb_skip hU hlt' fun q hq ⟨hq1, hq2⟩ ↦ ?_
          rcases hpc' q hq with h | h
          · omega
          · exact absurd hq2 (by show ¬ q.1 < pc' - (alignA e.I.t.name).X.entry; omega)
        · rw [ha] at harm; cases harm
    have hpt : pendAt (alignA e.I.t.name).X (alignA e.I.t.name).code (alignA e.I.t.name).d
        (pc' - entOf alignA e.I.t.name) = false := by
      rcases htgt with ht | ⟨z, x, arms, ss, a, k, hz, hzc, ha, hax, hk, hjt⟩
      · exact hF.tgt off oc od of hins pc' ht
      · have hmem : Stmt.match_ x arms ∈ stmtsOf (alignA e.I.t.name).body :=
          zok_stmts hz (by rw [Zip.pos, hzc]; simp)
        have ha' : (od, a) ∈ armsOf (B2C.plumbOf j) := by
          rw [alignA_of hj] at ha; exact arms_ofData ha
        exact hF.arm _ hmem x arms rfl od a k pc' ha' hax hk hjt
    rw [hnb, hpd, hpd] at *
    rw [hpt, h1, hfrAt, h2]
    simp only [Bool.cond_false, Nat.zero_mul, Nat.add_zero]
  | @skip e' oc od of c f σ' hI' hnc' hins hc hph hcase =>
    have hlt0 : e.nc < e.I.t.kids.length := (List.getElem?_eq_some_iff.mp hph).1
    have hcur : cursorAt alignA e' (off + 1) = cursorAt alignA e off + (treeSizes alignA e off).sum := by
      rw [cursorAt_unfold alignA e', hI', hnc', hstep', hnbS]
      rcases hcase with ⟨hnx, hlen⟩ | ⟨s, hs⟩
      · obtain ⟨h1, h2, h3⟩ := pend_nf hins rfl (noFrame_of hF hins (Or.inr (Or.inr (Or.inl hnx))))
        have hl := loop_of_nextAt hj hins hnx
        rw [hl] at hkC
        simp only [↓reduceIte] at hkC
        have hK : (((e.I.t.kidsC coreProgram.loop).take (e.nc + 1)).map (Tree.total B2C.fs)).sum =
            (((e.I.t.kidsC coreProgram.loop).take e.nc).map (Tree.total B2C.fs)).sum := by
          rw [take_map_sum_le (by omega), take_map_sum_le (by omega)]
        rw [hpd, h3, hpd, h1, hfrAt, h2, hK]
        simp only [Bool.cond_false, Nat.zero_mul, Nat.add_zero]
        rfl
      · have hPs : (B2C.plumbOf j).sites ≠ [] := by
          rw [alignA_of hj] at hs
          exact List.ne_nil_of_mem (siteAt_ofData hs).1
        obtain ⟨rr, hrr, -, hrj⟩ := hF.site hPs off oc od of hins (siteAt_some hs)
        obtain ⟨hsum, h3⟩ := pend_site hF.uniq hins rfl ⟨rr, hrr, hrj⟩
        have hnc : e.nc < (e.I.t.kidsC coreProgram.loop).length := by
          rw [hkC]
          split
          · have := hkl ▸ notLast_of_site hj hwj (by assumption) hc hs; omega
          · exact hlt0
        have hkc : (e.I.t.kidsC coreProgram.loop)[e.nc]? = some (.phantom f σ') := by
          rw [kidsC_getElem? hnc]; exact hph
        rw [ksum_succ hnc, hpd, h3, hkc, hfrAt, hpd, hsum]
        have hph' : (e.I.t.kidsC coreProgram.loop)[e.nc] = .phantom f σ' := by
          rw [List.getElem?_eq_some_iff] at hkc; exact hkc.2
        rw [hph']
        simp only [Bool.cond_false, Nat.zero_mul, Nat.add_zero, Option.map_some, Option.getD_some, Nat.one_mul]
        have hpb : Tree.total B2C.fs (Tree.phantom f σ') = Tree.block B2C.fs coreProgram.loop (Tree.phantom f σ') := by
          simp only [Tree.total, Tree.block]
        rw [hpb, ← Nat.add_assoc]
        rfl
    refine ⟨_, _, done', _, st, hr', hts', ?_, chainA_top hI' ?_ hch⟩
    · rw [hI', show entOf alignA e.I.t.name + off + 1 - entOf alignA e.I.t.name = off + 1 by omega]
      exact hcur
    · unfold TailA
      rw [hI', hnc']
      intro hl hle hne
      rcases hcase with ⟨-, hlen⟩ | ⟨s, hs⟩
      · exact phantom_last hph (by omega) hne
      · have := hkl ▸ notLast_of_site hj hwj hl hc hs
        omega
  | @push e' J fn oc od of c s hI' hnc' hins hc hsite hsr hat hJ hk hkf hfind hhdr =>
    have hPs : s ∈ (B2C.plumbOf j).sites := by
      rw [alignA_of hj] at hsite; exact (siteAt_ofData hsite).1
    obtain ⟨rr, hrr, -, hrj⟩ := hF.site (List.ne_nil_of_mem hPs) off oc od of hins (siteAt_some hsite)
    obtain ⟨hsum, -⟩ := pend_site hF.uniq hins rfl ⟨rr, hrr, hrj⟩
    have hz0 : (alignA e.I.t.name).X.zeroAt oc = false := by
      obtain ⟨oc', od', q', hc', -, h1, -⟩ := frameOk_spec (hF.frame rr hrr)
      rw [hrj, hins] at hc'
      cases hc'
      exact h1
    obtain ⟨hnbo, hnbt⟩ := hnone oc od of hins (by
      unfold bufJumpOk
      obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp (siteAt_some hsite)
      simp [hz0, hs'])
    have hlt0 : e.nc < e.I.t.kids.length := (List.getElem?_eq_some_iff.mp hk).1
    have hnl : coreProgram.loop e.I.t.name = true → e.nc + 1 < e.I.t.kids.length := fun hl ↦
      hkl ▸ notLast_of_site hj hwj hl hc hsite
    have hnc : e.nc < (e.I.t.kidsC coreProgram.loop).length := by
      rw [hkC]
      split
      · have := hnl (by assumption); omega
      · exact hlt0
    have hkc : (e.I.t.kidsC coreProgram.loop)[e.nc] = J.t := by
      have := kidsC_getElem? hnc
      rw [hk, List.getElem?_eq_getElem hnc] at this
      exact Option.some.inj this
    have hpos := kid_place hr hI hJ hk hkf
    rw [kid_pos hnc] at hpos
    obtain ⟨hJfp, hJcur⟩ := Prod.mk.inj (Option.some.inj hpos)
    have htake : (e.I.t.bufs.take (bufsOf (alignA e.I.t.name).X (alignA e.I.t.name).d).length).sum = e.I.t.bufs.sum :=
      take_sum_le hbl
    have hE' : EntOk coreProgram (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) e' :=
      hts'.track.ents e' (List.mem_cons_of_mem _ List.mem_cons_self)
    have hsr63 : s.r < 2 ^ 63 := by
      have := (entry_of_atPc progAl alLayout_alignA hE' hat).1
      rw [guest_logSize] at this
      omega
    refine ⟨_, _, done', _, e' :: st, hr', hts', ?_, tailA_enter J fn, ⟨s.r, hhdr, hsr63, ?_⟩, chainA_top hI' ?_ hch⟩
    · change cursorAt alignA (Ent.enter coreProgram J fn) (entOf alignA J.t.name - entOf alignA J.t.name) = _
      rw [Nat.sub_self, cursorAt_enter, hstep', hnbo, hfrAt, hpd, hsum, htake, ← hJcur,
        List.getElem?_eq_getElem hnc, hkc]
      simp only [Option.map_some, Option.getD_some, Nat.one_mul, Inst.curAt, List.take_length]
    · change J.endCur B2C.fs coreProgram.loop = cursorAt alignA e' (s.r - entOf alignA e'.I.t.name)
      have hret : pendIn (alignA e.I.t.name).code (frames (alignA e.I.t.name).X (alignA e.I.t.name).d)
          (s.r - entOf alignA e.I.t.name) = false := hF.ret s hPs
      rw [cursorAt_unfold alignA e', hI', hnc', hnbt _ (by omega), hpd, hret, htake,
        endCur_kid (fs := B2C.fs) hnc hkc.symm hJfp.symm (by rw [← hJcur, ← hJfp, hkc])]
      simp only [Inst.curAt, List.take_length, Bool.cond_false, Nat.zero_mul, Nat.add_zero]
    · unfold TailA
      rw [hI', hnc']
      intro hl hle
      have := hnl hl
      omega
  | @tail J fn oc od of hins hz0 hnx hlen hJ hk hkf hfind hhdr =>
    obtain ⟨h1, h2, -⟩ := pend_nf hins rfl (noFrame_of hF hins (Or.inr (Or.inr (Or.inl hnx))))
    obtain ⟨hnbo, -⟩ := hnone oc od of hins (by unfold bufJumpOk; simp [hz0, nextAt_selfAt hnx])
    have hl := loop_of_nextAt hj hins hnx
    have hkl' : e.I.t.kids.length = e.nc + 1 := hkl ▸ hlen
    rw [hl] at hkC
    simp only [↓reduceIte] at hkC
    have hne : e.I.t.kids ≠ [] := fun h ↦ by rw [h] at hkl'; simp at hkl'
    have hpos := kid_place hr hI hJ hk hkf
    rw [show e.nc = e.I.t.kids.length - 1 by omega, tail_pos hl hne] at hpos
    obtain ⟨-, hJcur⟩ := Prod.mk.inj (Option.some.inj hpos)
    have hJt : J.t = e.I.t.kids.getLast hne := by
      have h1 := List.getLast?_eq_some_getLast hne
      rw [List.getLast?_eq_getElem?, show e.I.t.kids.length - 1 = e.nc by omega, hk] at h1
      exact Option.some.inj h1
    have htake : (e.I.t.bufs.take (bufsOf (alignA e.I.t.name).X (alignA e.I.t.name).d).length).sum = e.I.t.bufs.sum :=
      take_sum_le hbl
    have hcur : cursorAt alignA (Ent.enter coreProgram J fn) 0 = cursorAt alignA e off + (treeSizes alignA e off).sum := by
      rw [cursorAt_enter, hstep', hnbo, hfrAt, h2, hpd, h1, htake, ← hJcur]
      simp only [Inst.curAt, List.take_length, Bool.cond_false, Nat.zero_mul, Nat.add_zero]
      rw [take_map_sum_le (by omega)]
    have hend : J.endCur B2C.fs coreProgram.loop = e.I.endCur B2C.fs coreProgram.loop :=
      endCur_tail hl hne hJt hJcur.symm hnode
    refine ⟨_, _, done', _, st, hr', hts', ?_, ?_⟩
    · change cursorAt alignA (Ent.enter coreProgram J fn) (entOf alignA J.t.name - entOf alignA J.t.name) = _
      rw [Nat.sub_self]; exact hcur
    · rcases st with _ | ⟨e2, st2⟩
      · exact tailA_enter J fn
      · obtain ⟨-, ⟨r0, hr0, hlt, he⟩, hrest⟩ := hch
        exact ⟨tailA_enter J fn, ⟨r0, by rw [← hr0]; exact hhdr, hlt, by
          change J.endCur B2C.fs coreProgram.loop = _; rw [hend]; exact he⟩, hrest⟩
  | @ret e2 st2 oc _ hins hz0 hmain hst hlen hhdr =>
    subst hst
    obtain ⟨h1, h2, -⟩ := pend_nf hins rfl (noFrame_of hF hins (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
    obtain ⟨hnbo, -⟩ := hnone oc 0 1 hins (by unfold bufJumpOk; simp [hz0])
    obtain ⟨htl, ⟨r1, hr1, hr1lt, hend⟩, hrest⟩ := hch
    have hE2 : EntOk coreProgram (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) e2 :=
      hts'.track.ents e2 List.mem_cons_self
    have hr0lt : pc' < 2 ^ 63 := by
      have := (entry_of_atPc progAl alLayout_alignA hE2 hts'.linked.top.2).1
      rw [guest_logSize] at this
      omega
    have hr10 : r1 = pc' := by
      have h := ofK_injective (hr1.symm.trans hhdr)
      exact gpow_inj (by omega) (by omega) h
    subst hr10
    have htake : (e.I.t.bufs.take (bufsOf (alignA e.I.t.name).X (alignA e.I.t.name).d).length).sum = e.I.t.bufs.sum :=
      take_sum_le hbl
    refine ⟨_, _, done', e2, st2, hr', hts', ?_, hrest⟩
    rw [← hend, endCur_ret hnode (fun hl hk ↦ htl hl (by omega) hk), hstep', hnbo, hfrAt, h2, hpd, h1, htake]
    simp only [Inst.curAt, List.take_length, Bool.cond_false, Nat.zero_mul, Nat.add_zero]
    rw [take_map_sum_le (l := e.I.t.kidsC coreProgram.loop) (n := e.nc) (by rw [hkC]; split <;> omega)]


/-- **Each step keeps `YAlloc alignA`**, from `SizesAt` alone. -/
theorem keepY_allocA_of (hS : SizesAt alignA) : KeepY (YAlloc alignA) :=
  keepY_allocA hS curArith_alignA

end

end LeanVM.Guest.EndExec
