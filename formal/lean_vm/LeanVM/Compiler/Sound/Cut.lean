/-
  LeanVM.Compiler.Sound.Cut

  A function's piece from its parts (`Compiler.Cut`): the walk glued at its cuts, between top-level
  statements and between the arms of a `match`, and the code chunk by chunk.
-/

module

public import LeanVM.Compiler.Cut
public import LeanVM.Compiler.Sound.Compiles

/-!
# Cut pieces glued

`pieceOk_of_cut`: if a function's walk from its start state reaches `st₁` at its first cut
(`placeHead`), each next cut from the one before (`placeBlockN`), and its end `st` from the last
cut (`placeTail`), and `fnPreOk`, `cutHeadOk` and every `cutChunkOk` hold of `st`, its piece holds:
`pieceOk … = true`, the very Bool `compiles_of_pieces` reads, with no evaluation of the whole walk.
The glue is the walk's own structure:

* `placeBlock_split`: a block's walk is its first `n` statements', then the rest's;
* `placeMatchStmt_eq`: a `match` statement's walk is `matchPre`, then `armsRun` of its arms, then
  `matchPost` (`placeArms_eq`: `placeArms` is `armsRun`, then the next free cell set past the
  longest arm); `armsRun_cut`: the arms' run is the first `m` arms' (`armsRunN`), then the rest's;
* `blockOps`, `blockFills`, `blockSize` are what emission gives (`emitFn_ops`, `emitFn_fills`,
  `emitFn_size`), so the code and the slots are checked on the placed statements by position.
-/

namespace LeanVM.Compiler

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- A walk that succeeds, then another: their sequence. -/
theorem P.bind_ok {α β : Type} {m : P α} {f : α → P β} {ctx : Ctx} {st st' : St} {a : α}
    (h : m ctx st = .ok (a, st')) : (m >>= f) ctx st = f a ctx st' := by
  show (do let (a, s) ← m ctx st; f a ctx s : Except String (β × St)) = _
  rw [h]
  rfl

/-- A sequence of walks that succeeds: the first succeeds, then the second from its state. -/
theorem P.bind_inv {α β : Type} {m : P α} {f : α → P β} {ctx : Ctx} {st st' : St} {b : β}
    (h : (m >>= f) ctx st = .ok (b, st')) :
    ∃ a s, m ctx st = .ok (a, s) ∧ f a ctx s = .ok (b, st') := by
  change (do let (a, s) ← m ctx st; f a ctx s : Except String (β × St)) = _ at h
  cases hm : m ctx st with
  | error e => rw [hm] at h; cases h
  | ok r => rw [hm] at h; exact ⟨r.1, r.2, rfl, h⟩

theorem placeBlock_cons (s : Stmt) (rest : List Stmt) :
    placeBlock (s :: rest) = (do placeStmt s rest; endStmt; placeBlock rest) := by
  rw [placeBlock]

/-- **A block's walk at a cut**: its first `n` statements, then the rest. -/
theorem placeBlock_split : ∀ (l : List Stmt) (n : ℕ),
    placeBlock l = (do placeBlockN l n; placeBlock (l.drop n))
  | [], n => by
      rw [placeBlockN, List.drop_nil, pure_bind]
  | _ :: _, 0 => by
      rw [placeBlockN, List.drop_zero, pure_bind]
  | s :: rest, n + 1 => by
      rw [placeBlock_cons, placeBlock_split rest n, placeBlockN, List.drop_succ_cons]
      simp only [bind_assoc]

theorem placeBlockN_add : ∀ (l : List Stmt) (n m : ℕ),
    placeBlockN l (n + m) = (do placeBlockN l n; placeBlockN (l.drop n) m)
  | [], n, m => by
      rw [placeBlockN, placeBlockN, List.drop_nil, placeBlockN, pure_bind]
  | s :: rest, 0, m => by
      rw [Nat.zero_add, placeBlockN, List.drop_zero, pure_bind]
  | s :: rest, n + 1, m => by
      rw [Nat.add_right_comm, placeBlockN, placeBlockN, placeBlockN_add rest n m, List.drop_succ_cons]
      simp only [bind_assoc]

/-- **Two consecutive cuts glued**: the walk to cut `k`, then over the next `m` statements. -/
theorem placeHead_add {tf : TracedFn} {k m : ℕ} {ctx : Ctx} {st st₁ st₂ : St}
    (h₁ : placeHead tf k ctx st = .ok ((), st₁))
    (h₂ : placeBlockN (tf.core.body.drop k) m ctx st₁ = .ok ((), st₂)) :
    placeHead tf (k + m) ctx st = .ok ((), st₂) := by
  have : placeHead tf (k + m) = (placeHead tf k >>= fun _ => placeBlockN (tf.core.body.drop k) m) := by
    simp only [placeHead, placeBlockN_add, bind_assoc]
  rw [this, P.bind_ok h₁, h₂]

/-- **A function's walk from its cut parts.** -/
theorem placeBody_of_cut {tf : TracedFn} {k : ℕ} {ctx : Ctx} {st st₁ st₂ : St}
    (h₁ : placeHead tf k ctx st = .ok ((), st₁)) (h₂ : placeTail tf k ctx st₁ = .ok ((), st₂)) :
    placeBody tf ctx st = .ok ((), st₂) := by
  have : placeBody tf = (placeHead tf k >>= fun _ => placeTail tf k) := by
    simp only [placeBody, placeHead, placeTail, placeParams, placeBlock_split tf.core.body k,
      bind_assoc]
  rw [this, P.bind_ok h₁, h₂]

/-! ## A `match` in parts -/

theorem placeArms_cons (arm : List Stmt) (more : List (List Stmt)) (j n : ℕ) (base : Cell)
    (exit : ArmExit) :
    placeArms (arm :: more) j n base exit =
      (do let r ← armStep arm j n base exit
          let blocks ← placeArms more (j + 1) n base exit
          modify fun s => { s with next := max s.next r.2 }
          pure (r.1 :: blocks)) := by
  rw [placeArms]
  cases exit <;> simp only [armStep, bind_assoc, pure_bind]

theorem modify_modify (f g : St → St) :
    (do modify f; modify g : P Unit) = modify (g ∘ f) := by
  funext ctx st
  rfl

/-- **`placeArms` is `armsRun`**, then the next free cell set past the longest arm. -/
theorem placeArms_eq : ∀ (arms : List (List Stmt)) (j n : ℕ) (base : Cell) (exit : ArmExit),
    placeArms arms j n base exit =
      (do let r ← armsRun arms j n base exit
          modify fun s => { s with next := r.2 }
          pure r.1)
  | [], j, n, base, exit => by
      rw [placeArms, armsRun, pure_bind]
  | arm :: more, j, n, base, exit => by
      rw [placeArms_cons, placeArms_eq more, armsRun]
      simp only [bind_assoc, pure_bind]
      congr 1

/-- **`placeMatch` in parts**: before the arms, the arms, after them. -/
theorem placeMatch_eq (x : V) (n : ℕ) (rest : List Stmt) (entered : Option (ℕ × Cell))
    (chained : Bool) (armsAt : Cell → ArmExit → P (List (List PStmt))) :
    placeMatch x n rest entered chained armsAt =
      (do let mc ← matchHeadOf x n rest entered chained
          let blocks ← armsAt mc.base mc.exit
          matchTail mc blocks) := by
  unfold placeMatch matchHeadOf
  simp only [bind_assoc]
  congr 1
  funext r
  rcases r with ⟨lx, nextSel, sfp, one⟩
  cases entered with
  | some p =>
    rcases p with ⟨first, join⟩
    cases nextSel with
    | some q =>
      rcases q with ⟨x', n'⟩
      simp only [bind_assoc, pure_bind, matchTail]
      rfl
    | none =>
      simp only [bind_assoc, pure_bind, matchTail]
      rfl
  | none =>
    cases nextSel with
    | some q =>
      rcases q with ⟨x', n'⟩
      simp only [bind_assoc, pure_bind, matchTail]
    | none => simp only [bind_assoc, pure_bind, matchTail]

/-- **A `match` statement's walk in parts**: before its arms, its arms, after them. -/
theorem placeMatchStmt_eq (x : V) (arms : List (List Stmt)) (rest : List Stmt) :
    (do placeStmt (.match_ x arms) rest; endStmt) =
      (do let mc ← matchPre x arms.length rest
          let r ← armsRun arms 0 arms.length mc.base mc.exit
          matchPost mc r.1 r.2) := by
  rw [placeStmt]
  simp only [placeMatch_eq, matchPre, matchPost, placeArms_eq, bind_assoc, pure_bind]

/-- **A `match` statement from its parts.** -/
theorem placeBlockN_match {x : V} {arms : List (List Stmt)} {rest : List Stmt} {ctx : Ctx}
    {st st₁ st₂ st₃ : St} {mc : MatchHead} {bs : List (List PStmt)} {t : Cell}
    (hpre : matchPre x arms.length rest ctx st = .ok (mc, st₁))
    (harms : armsRun arms 0 arms.length mc.base mc.exit ctx st₁ = .ok ((bs, t), st₂))
    (hpost : matchPost mc bs t ctx st₂ = .ok ((), st₃)) :
    placeBlockN (.match_ x arms :: rest) 1 ctx st = .ok ((), st₃) := by
  have hstmt : (do placeStmt (.match_ x arms) rest; endStmt) ctx st = .ok ((), st₃) := by
    rw [placeMatchStmt_eq, P.bind_ok hpre, P.bind_ok harms]
    exact hpost
  have : placeBlockN (.match_ x arms :: rest) 1 =
      ((do placeStmt (.match_ x arms) rest; endStmt) >>= fun _ => placeBlockN rest 0) := by
    rw [placeBlockN, bind_assoc]
  rw [this, P.bind_ok hstmt]
  cases rest <;> rfl

theorem drop_of_isMatchAt {body : List Stmt} {i : ℕ} (hs : isMatchAt body i = true) :
    body.drop i = .match_ (selOf (body.getD i default)) (armsOf (body.getD i default)) ::
      body.drop (i + 1) := by
  unfold isMatchAt at hs
  split at hs
  · next x arms rest h =>
    have hi : i < body.length := by
      have := congrArg List.length h
      simp only [List.length_drop, List.length_cons] at this
      omega
    have hget : body.getD i default = .match_ x arms := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      have := List.drop_eq_getElem_cons hi
      rw [h] at this
      exact (List.cons.inj this).1.symm
    rw [hget, h, selOf, armsOf]
    have := List.drop_eq_getElem_cons hi
    rw [h] at this
    rw [(List.cons.inj this).2]
  · cases hs

/-- **Statement `i` of a block, a `match`, from its parts.** -/
theorem placeBlockN_match_at {body : List Stmt} {i : ℕ} {ctx : Ctx} {st st₁ st₂ st₃ : St}
    {mc : MatchHead} {bs : List (List PStmt)} {t : Cell} (hs : isMatchAt body i = true)
    (hpre : matchPre (selOf (body.getD i default)) (armsOf (body.getD i default)).length
      (body.drop (i + 1)) ctx st = .ok (mc, st₁))
    (harms : armsRun (armsOf (body.getD i default)) 0 (armsOf (body.getD i default)).length
      mc.base mc.exit ctx st₁ = .ok ((bs, t), st₂))
    (hpost : matchPost mc bs t ctx st₂ = .ok ((), st₃)) :
    placeBlockN (body.drop i) 1 ctx st = .ok ((), st₃) := by
  rw [drop_of_isMatchAt hs]
  exact placeBlockN_match hpre harms hpost

/-- The arms' run reaches past `base`. -/
theorem armsRun_ge : ∀ {arms : List (List Stmt)} {j n : ℕ} {base : Cell} {exit : ArmExit}
    {ctx : Ctx} {st st' : St} {bs : List (List PStmt)} {t : Cell},
    armsRun arms j n base exit ctx st = .ok ((bs, t), st') → base ≤ t
  | [], _, _, _, _, _, _, _, _, _, h => by
      rw [armsRun] at h
      cases h
      exact Nat.le_refl _
  | _ :: _, _, _, _, _, _, _, _, _, _, h => by
      rw [armsRun] at h
      obtain ⟨⟨blk, top⟩, s₁, _, h⟩ := P.bind_inv h
      obtain ⟨⟨blocks, t'⟩, s₂, h₂, h⟩ := P.bind_inv h
      cases h
      exact Nat.le_trans (armsRun_ge h₂) (Nat.le_max_left _ _)

/-- **The arms' run split**: the first `m` arms (`armsRunN`), then the rest. -/
theorem armsRun_split : ∀ {l : List (List Stmt)} {j m n : ℕ} {base : Cell} {exit : ArmExit}
    {ctx : Ctx} {st st₁ st₂ : St} {bA bB : List (List PStmt)} {tA tB : Cell},
    armsRunN l j n base exit m ctx st = .ok ((bA, tA), st₁) →
    armsRun (l.drop m) (j + m) n base exit ctx st₁ = .ok ((bB, tB), st₂) →
    armsRun l j n base exit ctx st = .ok ((bA ++ bB, max tB tA), st₂)
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, h₁, h₂ => by
      rw [armsRunN] at h₁
      cases h₁
      rw [List.drop_nil, armsRun] at h₂
      cases h₂
      rw [armsRun, Nat.max_self]
      rfl
  | _ :: _, _, 0, _, _, _, _, _, _, _, _, _, _, _, h₁, h₂ => by
      rw [armsRunN] at h₁
      cases h₁
      rw [List.drop_zero, Nat.add_zero] at h₂
      rw [List.nil_append, Nat.max_eq_left (armsRun_ge h₂), h₂]
  | arm :: more, j, m + 1, _, _, _, _, _, _, _, _, _, _, _, h₁, h₂ => by
      rw [armsRunN] at h₁
      obtain ⟨⟨blk, top⟩, s₁, hs, h₁⟩ := P.bind_inv h₁
      obtain ⟨⟨blocks, t'⟩, s₂, hr, h₁⟩ := P.bind_inv h₁
      cases h₁
      rw [List.drop_succ_cons, show j + (m + 1) = j + 1 + m by omega] at h₂
      have ih := armsRun_split hr h₂
      rw [armsRun, P.bind_ok hs]
      show (armsRun more (j + 1) _ _ _ >>= _) _ s₁ = _
      rw [P.bind_ok ih, List.cons_append, ← Nat.max_assoc]
      rfl

/-- **The arms of a `match` in runs**: the `m` arms from arm `a`, then the arms from `b = a + m`. -/
theorem armsRun_cut {arms : List (List Stmt)} {a m b n : ℕ} {base : Cell} {exit : ArmExit}
    {ctx : Ctx} {st st₁ st₂ : St} {bA bB : List (List PStmt)} {tA tB t : Cell}
    (hb : a + m = b) (ht : max tB tA = t)
    (h₁ : armsRunN (arms.drop a) a n base exit m ctx st = .ok ((bA, tA), st₁))
    (h₂ : armsRun (arms.drop b) b n base exit ctx st₁ = .ok ((bB, tB), st₂)) :
    armsRun (arms.drop a) a n base exit ctx st = .ok ((bA ++ bB, t), st₂) := by
  subst hb ht
  rw [← List.drop_drop] at h₂
  exact armsRun_split h₁ h₂

/-- The arms' run past the last arm. -/
theorem armsRun_end {arms : List (List Stmt)} {b n : ℕ} {base : Cell} {exit : ArmExit}
    {ctx : Ctx} {st : St} (h : arms.length ≤ b) :
    armsRun (arms.drop b) b n base exit ctx st = .ok (([], base), st) := by
  rw [List.drop_eq_nil_of_le h, armsRun]
  rfl

/-- The arms' run from arm `0`. -/
theorem armsRun_drop_zero {arms : List (List Stmt)} {n : ℕ} {base : Cell} {exit : ArmExit}
    {ctx : Ctx} {st st' : St} {r : List (List PStmt) × Cell}
    (h : armsRun (arms.drop 0) 0 n base exit ctx st = .ok (r, st')) :
    armsRun arms 0 n base exit ctx st = .ok (r, st') := by
  rwa [List.drop_zero] at h

/-! ## A function's code from an instruction on -/

theorem drop_append_of_le {α : Type} {l₁ : List α} {k : ℕ} (l₂ : List α) (h : l₁.length ≤ k) :
    (l₁ ++ l₂).drop k = l₂.drop (k - l₁.length) := by
  rw [List.drop_append, List.drop_eq_nil_of_le h, List.nil_append]

theorem drop_append_of_lt {α : Type} {l₁ : List α} {k : ℕ} (l₂ : List α) (h : k < l₁.length) :
    (l₁ ++ l₂).drop k = l₁.drop k ++ l₂ := by
  rw [List.drop_append, Nat.sub_eq_zero_of_le (Nat.le_of_lt h), List.drop_zero]

mutual
theorem stmtOpsFrom_eq : ∀ (s : PStmt) (pos k : ℕ), stmtOpsFrom s pos k = (stmtOps s pos).drop k
  | .chain h join x entry one sfp firsts stages, pos, k => by
      rw [stmtOpsFrom, stmtOps]
      split
      · next hk => rw [drop_append_of_lt _ (by simpa using hk)]
      · next hk =>
        rw [drop_append_of_le _ (by simp; omega), stagesOpsFrom_eq]
        simp
  | .op _ _, _, _ => by simp [stmtOpsFrom]
  | .ite .., _, _ => by simp [stmtOpsFrom]
  | .call _ _, _, _ => by simp [stmtOpsFrom]
  | .loopNext .., _, _ => by simp [stmtOpsFrom]
  | .dispatch .., _, _ => by simp [stmtOpsFrom]
  | .ret _ _, _, _ => by simp [stmtOpsFrom]
  | .halt _ _ _, _, _ => by simp [stmtOpsFrom]

theorem blockOpsFrom_eq : ∀ (b : List PStmt) (pos k : ℕ),
    blockOpsFrom b pos k = (blockOps b pos).drop k
  | [], _, _ => by rw [blockOpsFrom, blockOps, List.drop_nil]
  | s :: ss, pos, k => by
      rw [blockOpsFrom, blockOps]
      split
      · next hk =>
        rw [drop_append_of_le _ (by rw [stmtOps_length]; exact hk), stmtOps_length,
          blockOpsFrom_eq ss]
      · next hk =>
        rw [drop_append_of_lt _ (by rw [stmtOps_length]; omega), stmtOpsFrom_eq s]

theorem armsOpsFrom_eq : ∀ (as : List (List PStmt)) (pos k : ℕ),
    armsOpsFrom as pos k = (armsOps as pos).drop k
  | [], _, _ => by rw [armsOpsFrom, armsOps, List.drop_nil]
  | a :: as, pos, k => by
      rw [armsOpsFrom, armsOps]
      split
      · next hk =>
        rw [drop_append_of_le _ (by rw [blockOps_length]; exact hk), blockOps_length,
          armsOpsFrom_eq as]
      · next hk =>
        rw [drop_append_of_lt _ (by rw [blockOps_length]; omega), blockOpsFrom_eq a]

theorem stagesOpsFrom_eq : ∀ (ss : List (List (List PStmt))) (pos k : ℕ),
    stagesOpsFrom ss pos k = (stagesOps ss pos).drop k
  | [], _, _ => by rw [stagesOpsFrom, stagesOps, List.drop_nil]
  | s :: ss, pos, k => by
      rw [stagesOpsFrom, stagesOps]
      split
      · next hk =>
        rw [drop_append_of_le _ (by rw [armsOps_length]; exact hk), armsOps_length,
          stagesOpsFrom_eq ss]
      · next hk =>
        rw [drop_append_of_lt _ (by rw [armsOps_length]; omega), armsOpsFrom_eq s]
end

/-! ## The piece from its parts -/

/-- `placeFn` from its walk and its other checks. -/
theorem placeFn_of_cut {loops : Loops} {sigs : SMap (ℕ × ℕ)} {t : Tables} {tf : TracedFn}
    {st : St} (hpre : fnPreOk loops tf st = true)
    (hbody : placeBody tf (ctxOf loops sigs tf) (initSt loops t tf) = .ok ((), st)) :
    placeFn loops sigs t tf = .ok (placedOf tf st) := by
  simp only [fnPreOk, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_true_eq] at hpre
  obtain ⟨⟨hreg, hret⟩, hlt⟩ := hpre
  unfold placeFn
  simp only [hreg, Bool.false_eq_true, ↓reduceIte]
  split
  · rw [hbody]
    simp only [Nat.not_le.mpr hlt, ↓reduceIte]
    rfl
  · next hne =>
    split at hret
    · next vs hvs => exact absurd hvs (hne vs)
    · cases hret

/-- A function's resolved code is its statements' instructions by position, resolved. -/
theorem resolvedFn_emitFn (l : Layout) (pc0 frame : ℕ) (p : PFn) :
    resolvedFn l pc0 { (emitFn p).1 with frameSize := frame } =
      (blockOps p.body 0).map (resolveOp l pc0 frame) := by
  rw [← emitFn_ops]
  simp [resolvedFn, opsOf]

/-- **A function's piece from its parts**: its placement, `pieceOk`'s comparisons but the code's,
and its code chunk by chunk. -/
theorem pieceOk_of_cut {loops : Loops} {sigs : SMap (ℕ × ℕ)} {l : Layout} {t : Tables}
    {tf : TracedFn} {o : FnOut} {pc0 frame : ℕ} {cf : CompiledFunction} {pf : Placed} {t' : Tables}
    (hplace : placeFn loops sigs t tf = .ok (pf, t'))
    (hhead : cutHeadOk t tf o pc0 cf pf t' = true)
    (hchunks : ∀ c < cf.chunks.length, cutChunkOk l pc0 frame cf pf c = true) :
    pieceOk loops sigs l t tf o pc0 frame cf = true := by
  simp only [cutHeadOk, Bool.and_eq_true, beq_iff_eq] at hhead
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hhead
  unfold pieceOk pieceOkWith
  rw [hplace]
  simp only [decide_eq_true_eq] at h3 h7
  have h4' : allPairs fillIs (emitFn pf.fn).2.toList o.fills = true := by
    rw [emitFn_fills]
    exact h4
  have h6' : (emitFn pf.fn).1.code.size = o.size := by rw [emitFn_size, h6]
  simp only [Bool.and_eq_true, beq_iff_eq, h1, h2, h3, h4', h5, h6', h7, h8, h9, and_true, true_and,
    decide_eq_true_eq, decide_true]
  rw [resolvedFn_emitFn, chunked_eq]
  have hlen : ((blockOps pf.fn.body 0).map (resolveOp l pc0 frame)).length = o.size := by
    rw [List.length_map, blockOps_length, h6]
  rw [hlen]
  apply List.ext_getElem
  · simp [h10]
  · intro i _ h2'
    have := hchunks i h2'
    simp only [cutChunkOk, blockOpsFrom_eq, decide_eq_true_eq, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2', Option.getD_some] at this
    simp [← this, List.map_drop, List.map_take]

/-- **Function `j`'s piece from its parts**, as `pieceAt` reads it. -/
theorem pieceAt_of_cut {loops : Loops} {sigs : SMap (ℕ × ℕ)} {l : Layout} {p : List TracedFn}
    {os : List FnOut} {cfs : List CompiledFunction} {j k : ℕ} {st₁ st : St}
    (h₁ : placeHead (p.getD j default) k (ctxOf loops sigs (p.getD j default))
      (initSt loops (tablesAt os j) (p.getD j default)) = .ok ((), st₁))
    (h₂ : placeTail (p.getD j default) k (ctxOf loops sigs (p.getD j default)) st₁ = .ok ((), st))
    (hhead : cutHeadAt loops p os cfs j st = true)
    (hchunks : ∀ c < (cfs.getD j noFunction).chunks.length, cutChunkAt l p os cfs j st c = true) :
    pieceAt loops sigs l p os cfs j = true := by
  simp only [cutHeadAt, Bool.and_eq_true] at hhead
  exact pieceOk_of_cut (placeFn_of_cut hhead.1 (placeBody_of_cut h₁ h₂)) hhead.2 hchunks

theorem pieceOkWith_of_pieceOk {test : VMap Loc → Bool} {loops : Loops} {sigs : SMap (ℕ × ℕ)}
    {l : Layout} {t : Tables} {tf : TracedFn} {o : FnOut} {pc0 frame : ℕ} {cf : CompiledFunction}
    {pf : Placed} {t' : Tables} (h : pieceOk loops sigs l t tf o pc0 frame cf = true)
    (hplace : placeFn loops sigs t tf = .ok (pf, t')) (hx : test pf.locs = true) :
    pieceOkWith test loops sigs l t tf o pc0 frame cf = true := by
  unfold pieceOk pieceOkWith at *
  rw [hplace] at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨h.1, hx⟩

/-- **Function `j`'s piece with a test, from its parts.** -/
theorem pieceAtWith_of_cut {extra : ℕ → VMap Loc → Bool} {loops : Loops} {sigs : SMap (ℕ × ℕ)}
    {l : Layout} {p : List TracedFn} {os : List FnOut} {cfs : List CompiledFunction} {j k : ℕ}
    {st₁ st : St}
    (h₁ : placeHead (p.getD j default) k (ctxOf loops sigs (p.getD j default))
      (initSt loops (tablesAt os j) (p.getD j default)) = .ok ((), st₁))
    (h₂ : placeTail (p.getD j default) k (ctxOf loops sigs (p.getD j default)) st₁ = .ok ((), st))
    (hhead : cutHeadAt loops p os cfs j st = true)
    (hx : extra j (placedOf (p.getD j default) st).1.locs = true)
    (hchunks : ∀ c < (cfs.getD j noFunction).chunks.length, cutChunkAt l p os cfs j st c = true) :
    pieceAtWith extra loops sigs l p os cfs j = true := by
  have h := pieceAt_of_cut h₁ h₂ hhead hchunks
  simp only [cutHeadAt, Bool.and_eq_true] at hhead
  exact pieceOkWith_of_pieceOk h (placeFn_of_cut hhead.1 (placeBody_of_cut h₁ h₂)) hx

/-- **The locations function `j` is placed at, from its parts**: the last state's. -/
theorem placedLocsAt_of_cutWalk {loops : Loops} {sigs : SMap (ℕ × ℕ)} {p : List TracedFn}
    {os : List FnOut} {cfs : List CompiledFunction} {j k : ℕ} {st₁ st : St}
    (h₁ : placeHead (p.getD j default) k (ctxOf loops sigs (p.getD j default))
      (initSt loops (tablesAt os j) (p.getD j default)) = .ok ((), st₁))
    (h₂ : placeTail (p.getD j default) k (ctxOf loops sigs (p.getD j default)) st₁ = .ok ((), st))
    (hhead : cutHeadAt loops p os cfs j st = true) :
    placedLocsAt loops sigs p os j = st.locs := by
  simp only [cutHeadAt, Bool.and_eq_true] at hhead
  rw [placedLocsAt, placeFn_of_cut hhead.1 (placeBody_of_cut h₁ h₂)]
  rfl

end
end LeanVM.Compiler
