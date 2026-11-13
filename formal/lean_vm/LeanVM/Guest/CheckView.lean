/-
  LeanVM.Guest.CheckView

  A window's check over a function's own view of the program, without the guest's data.
-/

module

public import LeanVM.Guest.Check
public import LeanVM.Guest.ExpTables
public import LeanVM.Guest.WalkTags

/-!
# A window's check, over a function's view

What a function's checks read, apart from its own code, core IR and certificate, is its callees'
signatures, the jump table and the semantic relations (`Cert.fxAt`). `Glob.ofSigs` is the context
made of just those, so that a check stated over it imports its callees' signatures and no other
function's data; `checkWin_congr` and `restrict_ofSigs` carry it to the whole program's
context (`Check.Link`, in `CheckWinC.lean`). `checkWinCF` is `checkWin` with the window's code
read past whole chunks first (`execWinCS`), as the kernel decides it.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Guest LeanVM.Guest.Check LeanVM.Guest.Exec

@[expose] public section

/-- A function's code from offset `a`, its whole chunks before skipped first. -/
def codeFrom (f : CompiledFunction) (a : ℕ) : List OffsetInstruction :=
  (f.chunks.drop (a / chunkSize)).flatten.drop (a % chunkSize)

/-- `execWin`, the window's code read by `codeFrom`. -/
def execWinC (F : Facts) (f : CompiledFunction) (a : ℕ) (env : List (ℕ × Sym))
    (b : ℕ) :
    Result :=
  pass F f.entryPc f.instructionCount ((codeFrom f a).take (b - a)) a (some (Cur.init a (envOf
      env))) [] [] 0

/-- `execWinS`, the window's code read by `codeFrom`. -/
def execWinCS (F : Facts) (f : CompiledFunction) (a : ℕ) (env : List (ℕ × Sym))
    (seeds : List ℕ) (b : ℕ) : Result :=
  pass F f.entryPc f.instructionCount ((codeFrom f a).take (b - a)) a (some (Cur.init a (envOf
      env))) (seeds.map fun t ↦ (t, envOf env)) [] 0

theorem drop_flatten_chunked {C : ℕ} (hC : 0 < C) : ∀ {cs : List (List OffsetInstruction)} {n : ℕ},
    chunked C cs n = true → ∀ a, cs.flatten.drop a = (cs.drop (a / C)).flatten.drop (a % C)
  | [], _, _, a => by simp
  | c :: cs, n, h, a => by
    by_cases ha : a < C
    · rw [Nat.div_eq_of_lt ha, Nat.mod_eq_of_lt ha, List.drop_zero]
    · have hq : a / C = (a - C) / C + 1 := Nat.div_eq_sub_div hC (by omega)
      have hr : a % C = (a - C) % C := Nat.mod_eq_sub_mod (by omega)
      unfold chunked at h
      split_ifs at h with hn
      · simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h
        obtain ⟨rfl, hl⟩ := h
        rw [hq, List.drop_succ_cons, List.drop_nil, List.flatten_nil, List.drop_nil, List.flatten_cons,
          List.flatten_nil, List.append_nil, List.drop_eq_nil_of_le (by omega)]
      · simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨hl, h'⟩ := h
        rw [hq, hr, List.drop_succ_cons, List.flatten_cons, List.drop_append,
          List.drop_eq_nil_of_le (by omega), List.nil_append, hl]
        exact drop_flatten_chunked hC h' (a - C)

theorem execWinC_eq_of {f : CompiledFunction} (hf : chunked chunkSize f.chunks f.instructionCount = true)
    (F : Facts) (a : ℕ) (env : List (ℕ × Sym)) (b : ℕ) :
    execWinC F f a env b = execWin F f a env b := by
  unfold execWinC execWin codeFrom CompiledFunction.code
  rw [← drop_flatten_chunked (by decide) hf]

theorem execWinCS_nil (F : Facts) (f : CompiledFunction) (a : ℕ) (env : List (ℕ × Sym)) (b : ℕ) :
    execWinCS F f a env [] b = execWinC F f a env b := rfl

theorem execWinCS_eq_of {f : CompiledFunction} (hf : chunked chunkSize f.chunks f.instructionCount = true)
    (F : Facts) (a : ℕ) (env : List (ℕ × Sym)) (seeds : List ℕ) (b : ℕ) :
    execWinCS F f a env seeds b = execWinS F f a env seeds b := by
  unfold execWinCS execWinS codeFrom CompiledFunction.code
  rw [← drop_flatten_chunked (by decide) hf]

end
end LeanVM.Guest.B2C

namespace LeanVM.Guest

open LeanVM.Guest.Check

@[expose] public section

/-- The semantic relations by tag (`WalkTags.lean`): `0` the exponent table with its window
section (`B1.ExpTables`, `B1.ExpWinTab`), which `verify_sub` and `main_loop4` assume of an argument;
`1` the checker's own (`Check.tagNe`, here unused); `tagGkr` the GKR layer loop's parity
(`GkrPar`); `tagTabs` `open_stacked`'s window table (`B1.WinTabs`); from `2^21` `level_queries`'
windows (`lqSem`); the others the windowed Merkle walk's (`walkSem`). -/
def globSem (t : ℕ) (rd : Core.Reader) (ws : List LeanVM.Parameters.E) : Prop :=
  match t with
  | 0 => B1.ExpTables rd (ws.getD 0 0) ∧ B1.ExpWinTab rd (ws.getD 0 0)
  | 1 => True
  | t => if t = tagGkr then
      GkrPar rd (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) (ws.getD 3 0)
    else if t = tagTabs then B1.WinTabs rd (ws.getD 0 0)
    else if 2 ^ 21 ≤ t then lqSem t rd ws else walkSem t rd ws

end
end LeanVM.Guest

namespace LeanVM.Guest.Check

open LeanVM.Guest LeanVM.Guest.Exec LeanVM.Guest.B2C

@[expose] public section

/-- The context of the functions `l`, by index with their signatures, the jump table `jt` and
the semantic relations `sem`: a function's view of the program. -/
def Glob.ofSigs (l : List (ℕ × Sig)) (jt : Trie ℕ) (sem : ℕ → Core.Reader → List LeanVM.Parameters.E → Prop) :
    Glob :=
  ⟨fun j ↦ match l.find? (·.1 == j) with
    | some p => p.2
    | none => Sig.none, fun j ↦ l.any (·.1 == j), jt, sem⟩

/-- A certificate with the powers of `g` `p` as its executor's. -/
def Cert.withPows (C : Cert) (p : PowTree) : Cert :=
  match C with
  | ⟨⟨env, fpOne, _, arms, scaled, armsT⟩, los, cells, ins, nret, callees, pre, post, mem, sem, cuts, ends,
      entered⟩ =>
    ⟨⟨env, fpOne, p, arms, scaled, armsT⟩, los, cells, ins, nret, callees, pre, post, mem, sem,
      cuts, ends, entered⟩

/-- **A context agreeing with a view on its functions**: `G` gives each of the functions `l` its
signature there and counts it good, so `G` as they see it is the view. -/
theorem restrict_ofSigs {G : Glob} {l : List (ℕ × Sig)} {jt : Trie ℕ}
    {sem : ℕ → Core.Reader → List LeanVM.Parameters.E → Prop}
    (hl : ∀ p ∈ l, G.sig p.1 = p.2 ∧ G.good p.1 = true) (hjt : G.jt = jt)
    (hsem : G.sem = sem) {cs : List ℕ} (hcs : cs = l.map (·.1)) :
    G.restrict cs = (Glob.ofSigs l jt sem).restrict cs := by
  refine Glob.restrict_congr (fun j hj ↦ ?_) hjt hsem
  rw [hcs] at hj
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome.mpr ⟨p, hp, beq_self_eq_true p.1⟩ : (l.find? (·.1 == p.1)).isSome)
  have hqb := List.find?_some hq
  have hqk : q.1 = p.1 := beq_iff_eq.mp hqb
  refine ⟨?_, ?_⟩
  · show G.sig p.1 = (match l.find? (·.1 == p.1) with | some p => p.2 | none => Sig.none)
    rw [hq, ← hqk]
    exact (hl q (List.mem_of_find?_eq_some hq)).1
  · show G.good p.1 = l.any (·.1 == p.1)
    rw [(hl p hp).2, List.any_eq_true.mpr ⟨p, hp, beq_self_eq_true p.1⟩]

@[simp] theorem Glob.restrict_jt (G : Glob) (cs : List ℕ) : (G.restrict cs).jt = G.jt := rfl

/-- A window's check reads the context only as its function's callees see it. -/
theorem checkWin_congr {G G' : Glob} {f : CompiledFunction} {cf : Core.Fn} {C : Cert} {main : Bool}
    {i : ℕ} (h : G.restrict C.callees = G'.restrict C.callees) :
    checkWin G f cf C main i = checkWin G' f cf C main i := by
  simp only [checkWin, Cert.fxAt, h]

/-- `checkWin`, the window's code read by `execWinCS`. -/
noncomputable def checkWinCF (G : Glob) (f : CompiledFunction) (cf : Core.Fn) (C : Cert) (main : Bool) (i : ℕ) :
    Bool :=
  match execWinCS C.facts f (C.cutAt i).J (C.cutAt i).env ((C.succAt i).drop 1) (C.endAt f i) with
  | ⟨segs, _⟩ => listSeq segs fun segs ↦ (index segs).seq fun idx ↦ (C.locAt i).seq fun loc ↦
      C.contOk i && C.insOk (listElementOrDefault C.ins i []) && covOk loc (C.stmtsAt cf i) &&
      linkedWeak idx segs (C.fxAt G f cf main i segs idx loc).wJ (C.fxAt G f cf main i segs idx loc).wenv &&
      (bif i == 0 then runAt loc 2 cf.params && main == C.facts.fpOne else true) &&
      (match segAt (C.fxAt G f cf main i segs idx loc) (C.cutAt i).J
          (bookOf (C.cutAt i).facts .nil) (C.cutAt i).bnd with
        | some st => st.seg.env.sub Sym.beq (envOf (C.cutAt i).env) &&
            winEnd C i idx (walkFrom (C.fxAt G f cf main i segs idx loc) (C.cutAt i).env (C.selAt i)
              (C.succAt i) (C.stmtsAt cf i) st)
        | none => false)

theorem checkWinCF_eq {f : CompiledFunction} (hf : chunked chunkSize f.chunks f.instructionCount = true)
    (G : Glob) (cf : Core.Fn) (C : Cert) (main : Bool) (i : ℕ) :
    checkWinCF G f cf C main i = checkWin G f cf C main i := by
  unfold checkWinCF checkWin
  rw [execWinCS_eq_of hf]
  rfl

end
end LeanVM.Guest.Check
