/-
  LeanVM.Guest.Bridge.AllocFast

  The allocation hints' check on the code over the code's jumps listed once, for the kernel: equal to
  `curCode`, which walks the code to the next jump at every frame hint it reads.
-/

module

public import LeanVM.Guest.Bridge.AllocDefs

/-!
# The allocation hints' check by the code's jumps

`curCode` reads each frame hint's next jump (`nextJump`, a walk of the code from the hint) and the
instruction there, in each of its conjuncts, and scans the whole code for its jumps three times.
`curCodeJ` lists the code's jumps once (`jumpsFrom`), each frame hint with its next jump once (`nextJ`,
from the list), and reads both from those lists; `curCode_eq_curCodeJ` equates the two, so that the
generated checks (`Bridge/AllocChk/`) run `curCodeJ` (`allocRest_of_fast`).
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Guest.Core
open LeanVM.Guest.Check (getF)

@[expose] public section

/-- The jumps of a code from offset `i`: each one's offset and operands. -/
def jumpsFrom : ℕ → List OffsetInstruction → List (ℕ × ℕ × ℕ × ℕ)
  | _, [] => []
  | i, ins :: rest => match ins with
    | .jump oc od of => (i, oc, od, of) :: jumpsFrom (i + 1) rest
    | _ => jumpsFrom (i + 1) rest

/-- A listed jump as its instruction. -/
def jumpIns (j : ℕ × ℕ × ℕ × ℕ) : OffsetInstruction := .jump j.2.1 j.2.2.1 j.2.2.2

/-- The first of the jumps `js` at or after offset `a`. -/
def jumpAt (js : List (ℕ × ℕ × ℕ × ℕ)) (a : ℕ) : Option (ℕ × ℕ × ℕ × ℕ) :=
  js.find? fun j ↦ Nat.ble a j.1

/-- `nextJump` from the jumps `js` of a code of length `len`. -/
def nextJ (js : List (ℕ × ℕ × ℕ × ℕ)) (len a : ℕ) : ℕ :=
  match jumpAt js a with
  | some j => j.1
  | none => max a len

/-- `frameOk` from the jumps `js`. -/
noncomputable def frameOkJ (X : AlignCtx) (js : List (ℕ × ℕ × ℕ × ℕ)) (a : ℕ) (h : Prover.Exec.Hint) : Bool :=
  (match h with
    | .alloc .. | .allocArm .. | .allocFrames .. => true
    | _ => false) &&
  match jumpAt js a, allocPtr h with
  | some (_, oc, od, q), some p => Nat.beq q p && !X.zeroAt oc && !X.selfAt q && !X.nextAt q &&
      !(Nat.beq od 0 && Nat.beq q 1)
  | _, _ => false

/-- `pendIn` over the frame hints with their next jumps. -/
def pendJ (frJ : List (ℕ × ℕ × Prover.Exec.Hint)) (off : ℕ) : Bool :=
  frJ.any fun r ↦ decide (r.2.1 < off) && decide (off ≤ r.1)

/-- `sitesOk`'s test of the jump at offset `i` through `q`, over the frame hints with their next jumps. -/
noncomputable def siteJ (X : AlignCtx) (frJ : List (ℕ × ℕ × Prover.Exec.Hint)) (i q : ℕ) : Bool :=
  (!(getF X.sites q).isSome || frJ.any (fun r ↦ allocPtr r.2.2 == some q && Nat.beq r.1 i)) &&
    decide ((frJ.filter fun r ↦ Nat.beq r.1 i).length ≤ 1)

/-- `targetsOk`'s test of a jump to `od`, over the frame hints with their next jumps. -/
noncomputable def targetJ (X : AlignCtx) (frJ : List (ℕ × ℕ × Prover.Exec.Hint)) (od : ℕ) : Bool :=
  match X.pcAt od with
  | some t => !pendJ frJ (t - X.entry)
  | none => true

/-- `bufsJumps`'s test of the jump at offset `i`. -/
noncomputable def bufJumpJ (X : AlignCtx) (bs : List (ℕ × Prover.Exec.Hint)) (i oc od of : ℕ) : Bool :=
  !(bs.any fun q ↦ decide (i < q.1)) || bufJumpOk X bs i oc od of

/-- **`curCode` over the code's jumps listed once**, each frame hint with its next jump. -/
noncomputable def curCodeJ (X : AlignCtx) (fs : ℕ) (loop : Bool) (P : B2C.Plumb) (code : List OffsetInstruction)
    (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : Bool :=
  d.2.2.all (fun p ↦ p.2.all (addrOk X fs loop)) &&
  let js := jumpsFrom 0 code
  Exec.listSeq (allocHints d) fun hs ↦
    Exec.listSeq ((hs.filter fun q ↦ isFrame X q.2).map fun q ↦ (nextJ js code.length q.1, q)) fun frJ ↦
    Exec.listSeq (hs.filter fun q ↦ isBuf X q.2) fun bs ↦
  js.all (fun j ↦ bufJumpJ X bs j.1 j.2.1 j.2.2.1 j.2.2.2) && bufsFirst X false hs &&
    frJ.all (fun r ↦ frameOkJ X js r.2.1 r.2.2) &&
    ((frJ.isEmpty && P.sites.isEmpty) ||
      (js.all (fun j ↦ siteJ X frJ j.1 j.2.2.2) && js.all (fun j ↦ targetJ X frJ j.2.2.1))) &&
    P.sites.all (fun s ↦ !pendJ frJ (s.r - X.entry))

/-- `allocRest` with `curCodeJ`. -/
noncomputable def allocRestJ (X : AlignCtx) (fs : ℕ) (loop : Bool) (P : B2C.Plumb) (body : List Stmt)
    (code : List OffsetInstruction) (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : Bool :=
  pairsA X fs (topAllocs body) (((allocHints d).filter fun q ↦ isBuf X q.2).map (·.2)) && curCodeJ X fs loop P code d

end

/-! ## `curCodeJ` is `curCode` -/

public section

variable {X : AlignCtx}

/-- A scan of a code testing each jump is a test of each entry of `jumpsFrom`. -/
private theorem scan_eq (f : ℕ → ℕ → ℕ → ℕ → Bool) (g : ℕ → List OffsetInstruction → Bool)
    (hnil : ∀ i, g i [] = true)
    (hcons : ∀ i ins rest, g i (ins :: rest) =
      ((match ins with
        | .jump oc od of => f i oc od of
        | _ => true) && g (i + 1) rest)) :
    ∀ i l, g i l = (jumpsFrom i l).all fun j ↦ f j.1 j.2.1 j.2.2.1 j.2.2.2
  | i, [] => hnil i
  | i, ins :: rest => by
    rw [hcons, scan_eq f g hnil hcons (i + 1) rest]
    cases ins <;> simp [jumpsFrom]

private theorem jumpsFrom_ge : ∀ (i : ℕ) (l : List OffsetInstruction), ∀ j ∈ jumpsFrom i l, i ≤ j.1
  | _, [] => by simp [jumpsFrom]
  | i, ins :: rest => by
    have ih := fun j hj ↦ Nat.le_of_succ_le (jumpsFrom_ge (i + 1) rest j hj)
    cases ins <;> simp only [jumpsFrom, List.forall_mem_cons] <;> first | exact ih | exact ⟨le_rfl, ih⟩

private theorem jumpAt_succ {js : List (ℕ × ℕ × ℕ × ℕ)} {a : ℕ} (h : ∀ j ∈ js, a + 1 ≤ j.1) :
    jumpAt js a = jumpAt js (a + 1) := by
  cases js with
  | nil => rfl
  | cons j js =>
    have := h j List.mem_cons_self
    simp [jumpAt, Nat.ble_eq, show a ≤ j.1 by omega, this]

private theorem nextJ_succ {js : List (ℕ × ℕ × ℕ × ℕ)} {len a : ℕ} (h : ∀ j ∈ js, a + 1 ≤ j.1)
    (hl : a + 1 ≤ len) : nextJ js len a = nextJ js len (a + 1) := by
  unfold nextJ
  rw [jumpAt_succ h]
  split <;> omega

private theorem nextJ_spec : ∀ (l : List OffsetInstruction) (i d : ℕ),
    i + d + (l.drop d).findIdx OffsetInstruction.isJump = nextJ (jumpsFrom i l) (i + l.length) (i + d) ∧
      l[d + (l.drop d).findIdx OffsetInstruction.isJump]? = (jumpAt (jumpsFrom i l) (i + d)).map jumpIns
  | [], i, d => by simp [jumpsFrom, nextJ, jumpAt]
  | ins :: rest, i, d + 1 => by
    obtain ⟨h1, h2⟩ := nextJ_spec rest (i + 1) d
    have hb : Nat.ble (i + 1 + d) i = false :=
      Bool.eq_false_iff.mpr fun h ↦ absurd (Nat.le_of_ble_eq_true h) (by omega)
    have hskip : jumpAt (jumpsFrom i (ins :: rest)) (i + 1 + d) = jumpAt (jumpsFrom (i + 1) rest) (i + 1 + d) := by
      cases ins <;> simp [jumpsFrom, jumpAt, hb]
    rw [show i + (d + 1) = i + 1 + d by omega, List.drop_succ_cons, List.length_cons,
      show i + (rest.length + 1) = i + 1 + rest.length by omega]
    refine ⟨?_, ?_⟩
    · unfold nextJ at h1 ⊢
      rw [hskip, ← h1]
    · rw [hskip, show d + 1 + (rest.drop d).findIdx OffsetInstruction.isJump =
        (d + (rest.drop d).findIdx OffsetInstruction.isJump) + 1 by omega, List.getElem?_cons_succ]
      exact h2
  | ins :: rest, i, 0 => by
    obtain ⟨h1, h2⟩ := nextJ_spec rest (i + 1) 0
    simp only [Nat.add_zero, List.drop_zero, Nat.zero_add] at h1 h2 ⊢
    by_cases hj : ins.isJump = true
    · obtain ⟨oc, od, of, rfl⟩ : ∃ oc od of, ins = .jump oc od of := by
        cases ins <;> simp_all [OffsetInstruction.isJump]
      simp [jumpsFrom, nextJ, jumpAt, jumpIns, List.findIdx_cons, OffsetInstruction.isJump]
    · have hjs : jumpsFrom i (ins :: rest) = jumpsFrom (i + 1) rest := by
        cases ins <;> simp_all [jumpsFrom, OffsetInstruction.isJump]
      have hge := jumpsFrom_ge (i + 1) rest
      simp only [List.findIdx_cons, hj, Bool.false_eq_true, ↓reduceIte, hjs, List.length_cons]
      refine ⟨?_, ?_⟩
      · rw [nextJ_succ hge (by omega), show i + (rest.length + 1) = i + 1 + rest.length by omega, ← h1]
        omega
      · rw [jumpAt_succ hge, List.getElem?_cons_succ, h2]

private theorem nextJump_eq_nextJ (code : List OffsetInstruction) :
    nextJump code = nextJ (jumpsFrom 0 code) code.length :=
  funext fun a ↦ by simpa only [nextJump, Nat.zero_add] using (nextJ_spec code 0 a).1

private theorem frameOk_eq_frameOkJ (code : List OffsetInstruction) (a : ℕ) (h : Prover.Exec.Hint) :
    frameOk X code a h = frameOkJ X (jumpsFrom 0 code) a h := by
  have hj : code[nextJump code a]? = (jumpAt (jumpsFrom 0 code) a).map jumpIns := by
    simpa only [nextJump, Nat.zero_add] using (nextJ_spec code 0 a).2
  unfold frameOk frameOkJ
  rw [hj]
  rcases jumpAt (jumpsFrom 0 code) a with _ | ⟨_, oc, od, q⟩ <;> cases allocPtr h <;> rfl

/-- **`curCodeJ` is `curCode`.** -/
theorem curCode_eq_curCodeJ (fs : ℕ) (loop : Bool) (P : B2C.Plumb) (code : List OffsetInstruction)
    (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : curCode X fs loop P code d = curCodeJ X fs loop P code d := by
  simp only [curCode, curCodeJ, Exec.listSeq_eq, ← nextJump_eq_nextJ]
  have hpend : ∀ (fr : List (ℕ × Prover.Exec.Hint)) off,
      pendIn code fr off = pendJ (fr.map fun q ↦ (nextJump code q.1, q)) off := fun fr off ↦ by
    simp [pendIn, pendJ, List.any_map, Function.comp_def]
  have hb : ∀ bs, bufsJumps X bs 0 code = (jumpsFrom 0 code).all fun j ↦ bufJumpJ X bs j.1 j.2.1 j.2.2.1 j.2.2.2 :=
    fun bs ↦ scan_eq _ (bufsJumps X bs) (fun _ ↦ rfl) (fun i ins rest ↦ by cases ins <;> rfl) 0 code
  have hs : ∀ fr, sitesOk X code fr 0 code = (jumpsFrom 0 code).all fun j ↦
      siteJ X (fr.map fun q ↦ (nextJump code q.1, q)) j.1 j.2.2.2 := fun fr ↦
    scan_eq (fun i _ _ q ↦ siteJ X (fr.map fun q ↦ (nextJump code q.1, q)) i q) (sitesOk X code fr) (fun _ ↦ rfl)
      (fun i ins rest ↦ by
        cases ins <;> simp [sitesOk, siteJ, List.any_map, List.filter_map, Function.comp_def]) 0 code
  have ht : ∀ fr, targetsOk X code fr code = (jumpsFrom 0 code).all fun j ↦
      targetJ X (fr.map fun q ↦ (nextJump code q.1, q)) j.2.2.1 := fun fr ↦
    scan_eq (fun _ _ od _ ↦ targetJ X (fr.map fun q ↦ (nextJump code q.1, q)) od) (fun _ l ↦ targetsOk X code fr l)
      (fun _ ↦ rfl) (fun i ins rest ↦ by
        cases ins with
        | jump oc od of =>
          simp only [targetsOk, targetJ]
          cases X.pcAt od <;> simp [hpend]
        | _ => rfl) 0 code
  rw [hb, hs, ht]
  simp [frameOk_eq_frameOkJ, hpend, List.all_map, Function.comp_def]

/-- **`allocRest` from the check over the code's jumps.** -/
theorem allocRest_of_fast {fs : ℕ} {loop : Bool} {P : B2C.Plumb} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (h : allocRestJ X fs loop P body code d = true) :
    allocRest X fs loop P body code d = true := by
  rwa [allocRest, curCode_eq_curCodeJ]

end

end LeanVM.Guest.Bridge
