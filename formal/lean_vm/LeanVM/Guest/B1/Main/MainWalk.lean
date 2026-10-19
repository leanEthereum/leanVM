/-
  LeanVM.Guest.B1.Main.MainWalk

  The path of `main`'s body: its straight-line segments and its two branches, read as one
  straight-line block for the branches the valuation takes.
-/

module

public import LeanVM.Guest.B1.Main.Straight
public import LeanVM.Guest.B1.Main.Template
public import LeanVM.Guest.B1.Uniform

/-!
# `main`'s path

`main`'s body walks the straight-line block `mainLin b1 b2` (the direct DA branch when `b1`, the leaf's branch
when `b2`, the batching branch otherwise), with the two branch conditions' `inK` events
interleaved, which no frame, `HeapBuf`, `frameAddr` or load reads (`walk_mainBody`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

theorem walk_straight_fall (σ : Val) (pre : List Stmt) (h : pre.all Stmt.straight = true) :
    walk σ pre = .fall (pre.flatMap (slEvs σ)) := by
  have := LeanVM.Guest.B1.walk_pre_straight σ [] pre h
  rw [List.append_nil] at this
  rw [this]; simp [walk, Out.pre]

/-- `mainPost`'s statements before its return. -/
def mainPostPre : List Stmt := mainPost.dropLast

theorem mainPost_eq : mainPost = mainPostPre ++ [.ret []] := by
  simp [mainPost, mainPostPre]

/-- **`main` as one straight-line block**, the direct DA branch when `b1`, the leaf's branch
when `b2`. -/
def mainLin (b1 b2 : Bool) : List Stmt :=
  mainPre ++ (if b1 then daBranch else []) ++ mainMid ++ (if b2 then leafT else aggT) ++ mainPostPre

set_option maxRecDepth 100000 in
theorem mainLin_straight (b1 b2 : Bool) : (mainLin b1 b2).all Stmt.straight = true := by
  cases b1 <;> cases b2 <;> decide +kernel

/-- The events of `main`'s path: `mainLin`'s, the branch conditions' `inK` among them. -/
noncomputable def mainEvs (σ : Val) : List Ev :=
  mainPre.flatMap (slEvs σ) ++ .inK (.n 112) ::
    ((if σ (.n 112) = 0 then daBranch else []).flatMap (slEvs σ) ++
      (mainMid.flatMap (slEvs σ) ++ .inK (.n 155) ::
        ((if σ (.n 155) = 0 then leafT else aggT).flatMap (slEvs σ) ++
          mainPostPre.flatMap (slEvs σ))))

set_option maxRecDepth 100000 in
theorem walk_mainBody (σ : Val) : walk σ mainBody = .ret (mainEvs σ) [] := by
  have s1 : mainPre.all Stmt.straight = true := by decide +kernel
  have s2 : daBranch.all Stmt.straight = true := by decide +kernel
  have s3 : mainMid.all Stmt.straight = true := by decide +kernel
  have s4 : leafT.all Stmt.straight = true := by decide +kernel
  have s5 : aggT.all Stmt.straight = true := by decide +kernel
  have s6 : mainPostPre.all Stmt.straight = true := by decide +kernel
  have hb1 : walk σ (if σ (.n 112) = 0 then daBranch else []) =
      .fall ((if σ (.n 112) = 0 then daBranch else []).flatMap (slEvs σ)) :=
    walk_straight_fall σ _ (by split <;> simp_all)
  have hb2 : walk σ (if σ (.n 155) = 0 then leafT else aggT) =
      .fall ((if σ (.n 155) = 0 then leafT else aggT).flatMap (slEvs σ)) :=
    walk_straight_fall σ _ (by split <;> simp_all)
  have i1 : walk1 σ (.ite (.n 112) daBranch []) =
      .fall (.inK (.n 112) :: (if σ (.n 112) = 0 then daBranch else []).flatMap (slEvs σ)) := by
    by_cases h : σ (.n 112) = 0 <;> simp [walk1, h, Out.pre, walk_straight_fall σ _ s2, walk]
  have i2 : walk1 σ (.ite (.n 155) leafT aggT) =
      .fall (.inK (.n 155) :: (if σ (.n 155) = 0 then leafT else aggT).flatMap (slEvs σ)) := by
    by_cases h : σ (.n 155) = 0 <;>
      simp [walk1, h, Out.pre, walk_straight_fall σ _ s4, walk_straight_fall σ _ s5]
  rw [mainBody, LeanVM.Guest.B1.walk_pre_straight σ _ mainPre s1, walk, i1, Out.seq,
    LeanVM.Guest.B1.walk_pre_straight σ _ mainMid s3,
    walk, i2, Out.seq, mainPost_eq, walk_straight σ [] mainPostPre s6]
  simp only [Out.pre, mainEvs, List.cons_append]

/-- An extractor reading no `inK` event. -/
theorem filterMap_mainEvs {α : Type} (σ : Val) (g : Ev → Option α) (hg : ∀ c, g (.inK c) = none) :
    (mainEvs σ).filterMap g =
      ((mainLin (decide (σ (.n 112) = 0)) (decide (σ (.n 155) = 0))).flatMap (slEvs σ)).filterMap g := by
  simp only [mainEvs, mainLin, List.flatMap_append, List.filterMap_append, List.filterMap_cons, hg]
  by_cases h1 : σ (.n 112) = 0 <;> by_cases h2 : σ (.n 155) = 0 <;>
    simp [h1, h2, List.append_assoc]

theorem allocDsts_mainEvs (σ : Val) : allocDsts (mainEvs σ) =
    allocDsts ((mainLin (decide (σ (.n 112) = 0)) (decide (σ (.n 155) = 0))).flatMap (slEvs σ)) :=
  filterMap_mainEvs σ _ fun _ => rfl

theorem allocs_mainEvs (σ : Val) : allocs σ (mainEvs σ) =
    allocs σ ((mainLin (decide (σ (.n 112) = 0)) (decide (σ (.n 155) = 0))).flatMap (slEvs σ)) :=
  filterMap_mainEvs σ _ fun _ => rfl

theorem addrs_mainEvs (σ : Val) : addrs (mainEvs σ) =
    addrs ((mainLin (decide (σ (.n 112) = 0)) (decide (σ (.n 155) = 0))).flatMap (slEvs σ)) :=
  filterMap_mainEvs σ _ fun _ => rfl

theorem calls_mainEvs (σ : Val) : calls (mainEvs σ) =
    calls ((mainLin (decide (σ (.n 112) = 0)) (decide (σ (.n 155) = 0))).flatMap (slEvs σ)) :=
  filterMap_mainEvs σ _ fun _ => rfl

theorem loadAddrs_mainEvs (σ : Val) : loadAddrs σ (mainEvs σ) =
    loadAddrs σ ((mainLin (decide (σ (.n 112) = 0)) (decide (σ (.n 155) = 0))).flatMap (slEvs σ)) :=
  filterMap_mainEvs σ _ fun _ => rfl

/-! ## The block's parts -/

/-- `main`'s `HeapBuf` hints, in order. -/
def mainAllocs : List (V × (ℕ ⊕ V)) :=
  [(.n 69, .inr (.n 68)), (.n 77, .inr (.n 76)), (.n 80, .inr (.n 79)), (.n 102, .inl 2),
    (.n 103, .inr (.n 58)), (.n 123, .inr (.n 122)), (.n 133, .inr (.n 132)),
    (.n 142, .inr (.n 141)), (.n 145, .inr (.n 144)), (.n 153, .inl 53)]

/-- `main`'s calls of the claim lists and the raw signatures. -/
def mainFronts8 : List (Option V × String × List V × List V) :=
  [(some (.n 71), "__loop0", [.n 72, .n 50, .n 69], []),
    (none, "da_list_digest", [.n 69, .n 40], [.n 73, .n 74]),
    (none, "claim_list_digest", [.n 77, .n 0, .n 66], [.n 81, .n 82]),
    (none, "claim_list_digest", [.n 80, .n 3, .n 66], [.n 83, .n 84]),
    (some (.n 86), "__loop1", [.n 87, .n 1, .n 77, .n 0], []),
    (some (.n 89), "__loop2", [.n 90, .n 4, .n 80, .n 3], []),
    (some (.n 106), "__loop3", [.n 107, .n 2, .n 55, .n 103, .n 77], []),
    (some (.n 109), "__loop4", [.n 110, .n 5, .n 56, .n 103, .n 55, .n 2, .n 80], [])]

/-- The direct DA branch's calls. -/
def mainFrontsDa : List (Option V × String × List V × List V) :=
  [(none, "da_verify", [.n 66], [.n 113, .n 114, .n 115, .n 116]),
    (none, "cover_da_root", [.n 69, .n 104, .n 50, .n 117], [.n 118, .n 119, .n 120, .n 121])]

/-- The children's loop. -/
def mainFront5 : Option V × String × List V × List V :=
  (some (.n 149), "__loop5", [.n 150, .n 6, .n 145, .n 77, .n 103, .n 55, .n 66, .n 80, .n 56,
    .n 142, .n 69, .n 104, .n 50, .n 63, .n 64, .n 123, .n 65, .n 133], [])

/-- The batching call. -/
def mainFrontAgg : Option V × String × List V × List V :=
  (none, "aggregate_claims", [.n 6, .n 123, .n 133, .n 142, .n 153], [])

/-- The statement's digest. -/
def mainFrontSd : Option V × String × List V × List V :=
  (none, "statement_digest", [.n 63, .n 64, .n 102, .n 73, .n 74, .n 153], [.n 209, .n 210])

/-- `main`'s calls after `exponent_tables`, the direct DA branch's when `b1`, the batching's
unless `b2`. -/
def mainFronts (b1 b2 : Bool) : List (Option V × String × List V × List V) :=
  mainFronts8 ++ (if b1 then mainFrontsDa else []) ++ [mainFront5] ++
    (if b2 then [] else [mainFrontAgg]) ++ [mainFrontSd]

/-- The leaf's stores into `defer_stmt`. -/
def leafLoads : List (V × ℕ) :=
  (List.range 22).map (fun k => (.n 153, k)) ++ [(.n 153, 22)] ++
    (List.range 28).map (fun k => (.n 153, 23 + k)) ++ [(.n 153, 51), (.n 153, 52)]

set_option maxRecDepth 100000 in
theorem mainLin_parts (b1 b2 : Bool) : (mainLin b1 b2).filterMap Stmt.allocSz = mainAllocs ∧
    (mainLin b1 b2).filterMap Stmt.addrS = [] ∧
    (mainLin b1 b2).filterMap Stmt.callS =
      (none, "exponent_tables", [], [.n 65, .n 66]) :: mainFronts b1 b2 ∧
    (mainLin b1 b2).filterMap LeanVM.Guest.B1.Stmt.loadS =
      [(.n 102, 0), (.n 102, 1), (.n 145, 0), (.n 151, 0)] ++ (if b2 then leafLoads else []) ++
        [(.n 211, 0), (.n 215, 0)] := by
  cases b1 <;> cases b2 <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end
end LeanVM.Guest.B1.Main
