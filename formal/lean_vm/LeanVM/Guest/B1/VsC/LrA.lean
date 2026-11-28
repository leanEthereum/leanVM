/-
  LeanVM.Guest.B1.VsC.LrA

  `level_residual` completes placed: its `chain` buffer at its cursor, its two loops by the transfer.
-/

module

public import LeanVM.Guest.B1.VsC.LrTable
public import LeanVM.Guest.B1.VsC.SlowA
public import LeanVM.Guest.B1.Whir.HelperAll

/-!
# `level_residual`, placed

`level_residual__L{cols}_L{nhs}_L{hbits}` at `q = resBatch·b + r` queries (`resBatch ≤ q`) on
`[positions, row, hs, μ, g^b, g^r]` allocates its `chain` (`2(b + r + 1)` words at its cursor `c`,
its own words the honest chain `lrChainL`), runs the batches' loop from `g^0` (entered, `1 ≤ b`),
then the rest's loop (entered iff `r ≠ 0`), and returns the last pair, `lrPair … q`.

* `lrPre`, `lrBody_eq`: the body, `resBatch`'s powers unrolled; `lrσ` its valuation.
* `lrA_complete'`: one specialization, by `callAtA_node`, each loop by the transfer
  `callAtA_of_callCompletes0` from `lr1_loop` / `lr2_loop`, its shape `lr1_shape` / `lr2_shape`.
* `lrA_complete`: every entry of `lrTable`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.Value LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## Straight paths -/

/-- An atom event of a straight path is an atom of its body. -/
theorem mem_atom_slEvs {σ : Val} {a : Atom} : ∀ {pre : List Stmt}, Ev.atom a ∈ pre.flatMap (slEvs σ) →
    Stmt.atom a ∈ pre
  | [], h => by simp at h
  | s :: pre, h => by
    rw [List.flatMap_cons, List.mem_append] at h
    rcases h with h | h
    · cases s with
      | atom b =>
        simp only [slEvs, List.mem_singleton, Ev.atom.injEq] at h
        subst h; exact List.mem_cons_self
      | callIf c f args =>
        simp only [slEvs, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h
        · cases h
        · split at h <;> cases h
      | call f args rets => simp [slEvs] at h
      | _ => simp [slEvs] at h
    · exact List.mem_cons_of_mem _ (mem_atom_slEvs h)

/-- **A straight path's events hold** where its atoms hold and its guards are in `K`. -/
theorem holds_slEvs {rd : Reader} {σ : Val} : ∀ pre : List Stmt,
    (∀ a, Stmt.atom a ∈ pre → a.Holds rd σ) → (∀ c f args, Stmt.callIf c f args ∈ pre → IsInK (σ c)) →
    ∀ ev ∈ pre.flatMap (slEvs σ), ev.Holds rd σ
  | [], _, _ => by simp
  | s :: pre, ha, hc => by
    intro ev hev
    rw [List.flatMap_cons, List.mem_append] at hev
    rcases hev with hev | hev
    · cases s with
      | atom a =>
        simp only [slEvs, List.mem_singleton] at hev
        subst hev; exact ha a List.mem_cons_self
      | call f args rets =>
        simp only [slEvs, List.mem_singleton] at hev
        subst hev; trivial
      | callIf c f args =>
        simp only [slEvs, List.mem_cons, List.not_mem_nil, or_false] at hev
        rcases hev with rfl | rfl
        · exact hc c f args List.mem_cons_self
        · split <;> trivial
      | _ => simp [slEvs] at hev
    · exact holds_slEvs pre (fun a h => ha a (List.mem_cons_of_mem _ h))
        (fun c f args h => hc c f args (List.mem_cons_of_mem _ h)) ev hev

/-- A projection of a straight path's events blind to its guards and calls is its atoms'. -/
theorem flatMap_slEvs {α : Type} (g : Ev → List α) (σ : Val) (hk : ∀ c, g (.inK c) = [])
    (hs : ∀ f a, g (.skip f a) = []) (hc : ∀ f a r, g (.call f a r) = []) :
    ∀ pre : List Stmt, (pre.flatMap (slEvs σ)).flatMap g =
      pre.flatMap fun s => match s with | .atom a => g (.atom a) | _ => []
  | [] => rfl
  | s :: pre => by
    rw [List.flatMap_cons, List.flatMap_append, flatMap_slEvs g σ hk hs hc pre, List.flatMap_cons]
    congr 1
    cases s with
    | atom a => simp [slEvs]
    | call f args rets => simp [slEvs, hc]
    | callIf c f args => by_cases h : σ c = 0 <;> simp [slEvs, h, hk, hs, hc]
    | _ => simp [slEvs]

/-- A projection of a straight path's events blind to its guards and calls is its atoms'. -/
theorem filterMap_slEvs {α : Type} (g : Ev → Option α) (σ : Val) (hk : ∀ c, g (.inK c) = none)
    (hs : ∀ f a, g (.skip f a) = none) (hc : ∀ f a r, g (.call f a r) = none) :
    ∀ pre : List Stmt, (pre.flatMap (slEvs σ)).filterMap g =
      pre.filterMap fun s => match s with | .atom a => g (.atom a) | _ => none
  | [] => rfl
  | s :: pre => by
    rw [List.flatMap_cons, List.filterMap_append, filterMap_slEvs g σ hk hs hc pre, List.filterMap_cons]
    cases s with
    | atom a => cases h : g (.atom a) <;> simp [slEvs, h]
    | call f args rets => simp [slEvs, hc]
    | callIf c f args => by_cases h : σ c = 0 <;> simp [slEvs, h, hk, hs, hc]
    | _ => simp [slEvs]

/-- A loop helper's body of atoms passing `loadOkB` places nothing. -/
theorem unplaced_of_loadOk {ps : List (ℕ × ℕ)} {a : Atom} (h : loadOkB ps a = true) : atomUnplaced a = true := by
  cases a with
  | hint hh => simp [loadOkB] at h
  | frameAddr p run => simp [loadOkB, needsSide] at h
  | _ => rfl

/-- **A flat loop helper places nothing** and calls only itself. -/
theorem pureIn_loopFlat {self : String} {fn : Fn} {A : List Atom} {g : ℕ} {targs : List V}
    {ps : List (ℕ × ℕ)} (hfind : coreProgram.find? self = some fn)
    (hbody : fn.body = (A.map Stmt.atom ++ [Stmt.callIf (.n g) self targs]) ++ [.ret []])
    (hok : A.all (loadOkB ps) = true) : coreProgram.PureIn [self] := by
  intro f hf fn' hfn
  simp only [List.mem_singleton] at hf
  subst hf
  rw [hfind, Option.some.injEq] at hfn
  subst hfn
  rw [hbody, List.append_assoc]
  clear hbody hfind
  induction A with
  | nil => simp [Stmt.pureList, Stmt.pure]
  | cons a A ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hok
    simp only [List.map_cons, List.cons_append, Stmt.pureList, Stmt.pure, unplaced_of_loadOk hok.1,
      Bool.true_and]
    exact ih hok.2

/-- A flat loop helper is a loop helper. -/
theorem loop_loopFlat {self : String} {fn : Fn} {A : List Atom} {g : ℕ} {targs : List V}
    (hfind : coreProgram.find? self = some fn)
    (hbody : fn.body = (A.map Stmt.atom ++ [Stmt.callIf (.n g) self targs]) ++ [.ret []]) :
    coreProgram.loop self = true := by
  have hn : fn.name = self := by simpa using List.find?_some hfind
  rw [Program.loop_of_find? hfind, Fn.loop, hbody]
  simp [List.reverse_append, hn]

/-! ## `level_residual`'s body and valuation -/

/-- `level_residual`'s body before its return, `resBatch`'s square-and-multiply unrolled. -/
def lrPre (l1 l2 : String) : List Stmt :=
  [osMul 6 4 5, osCst 7 (gw 1), osMul 8 6 7, osMul 9 8 8, .atom (.hint (.allocDyn (.n 10) (.n 9))),
    osCst 11 (word 0 0), osLd 11 10 0, osCst 12 (word 0 0), osLd 12 10 1,
    osCst 13 (gw 0), osAdd 14 13 4, osCst 15 (gw 0),
    .callIf (.n 14) l1 [.n 15, .n 4, .n 0, .n 10, .n 1, .n 2, .n 3],
    osMul 16 4 4, osMul 17 10 16, osMul 18 4 4, osMul 19 18 18, osMul 20 19 19, osMul 21 0 20,
    osCst 22 (gw 0), osAdd 23 22 5, osCst 24 (gw 0),
    .callIf (.n 23) l2 [.n 24, .n 5, .n 17, .n 21, .n 1, .n 2, .n 3],
    osMul 25 5 5, osMul 26 17 25, osLd 27 26 0, osLd 28 26 1]

theorem lr_digits : osPowDigits resBatch = [false, false, false] := by decide +kernel

theorem lrBody_eq (l1 l2 : String) : lrBody l1 l2 = lrPre l1 l2 ++ [.ret [.n 27, .n 28]] := by
  simp only [lrBody, osPowLen, lr_digits, osLoopCallR]
  rfl

theorem lrPre_straight (l1 l2 : String) : (lrPre l1 l2).all Stmt.straight = true := rfl

theorem lr_calls (σ : Val) (l1 l2 : String) : calls ((lrPre l1 l2).flatMap (slEvs σ)) =
    [⟨l1, [.n 15, .n 4, .n 0, .n 10, .n 1, .n 2, .n 3], [], decide (σ (.n 14) ≠ 0)⟩,
      ⟨l2, [.n 24, .n 5, .n 17, .n 21, .n 1, .n 2, .n 3], [], decide (σ (.n 23) ≠ 0)⟩] := by
  rw [(straight_parts σ _ (lrPre_straight l1 l2)).2.2.2]
  rfl

theorem lr_quiet (l1 l2 : String) :
    (lrPre l1 l2).all (fun s => match s with | .atom a => atomQuiet a | _ => true) = true := rfl

theorem lr_triv (l1 l2 : String) :
    (lrPre l1 l2).all (fun s => match s with | .atom a => trivExact a | _ => true) = true := rfl

/-- `level_residual`'s valuation at `b` batches and `r` single steps, its chain at `c`, `P` its
returns. -/
def lrσ (ip irow ihs c : ℕ) (mu : E) (b r : ℕ) (P : E × E) : Val := fun v =>
  [ptrAt ip, ptrAt irow, ptrAt ihs, mu, gen ^ b, gen ^ r, gen ^ (b + r), gen ^ 1, gen ^ (b + r + 1),
    gen ^ (2 * (b + r + 1)), ptrAt c, 0, 0, gen ^ 0, gen ^ 0 + gen ^ b, gen ^ 0,
    gen ^ (2 * b), ptrAt (c + 2 * b), gen ^ (2 * b), gen ^ (4 * b), gen ^ (resBatch * b),
    ptrAt (ip + resBatch * b), gen ^ 0, gen ^ 0 + gen ^ r, gen ^ 0, gen ^ (2 * r),
    ptrAt (c + 2 * b + 2 * r), P.1, P.2].getD v.idx 0

/-! ## `level_residual`, placed -/

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

variable (fs al cert) in
/-- What `level_residual__L{cols}_L{nhs}_L{hbits}`'s placed completeness gives: at frame `fp`
and cursor `c`, on `q` positions at `ptrAt ip`, the row at `ptrAt irow`, the high part at
`ptrAt ihs` (cells of the region `R` its caller hands it), it returns the chains over the `q`
positions, its `chain` its own words at `c`. -/
def LrA (kd : ℕ) (name : String) (cols nhs hbits : ℕ) : Prop :=
  ∀ (q ip irow ihs : ℕ) (mu : E) (D Pos : ℕ → E) (hsv : List E) (R : ℕ → Prop),
    resBatch ≤ q → q < 2 ^ 30 → hsv.length = nhs →
    (∀ i < q, R (ip + i)) → (∀ i < cols, R (irow + i)) → (∀ i < nhs, R (ihs + i)) →
    ∀ fp c, fp + fs name ≤ c → ∃ e, CallAtA fs al cert kd name
      [ptrAt ip, ptrAt irow, ptrAt ihs, mu, gen ^ (q / resBatch), gen ^ (q % resBatch)]
      [(lrPair (lrP cols D) (lrH cols nhs hbits hsv) mu Pos q).1,
        (lrPair (lrP cols D) (lrH cols nhs hbits hsv) mu Pos q).2]
      R (fun _ => False) (fun _ => True)
      (fun rd => ReadsAt rd (ptrAt ip) (posL q Pos) ∧ ReadsAt rd (ptrAt irow) ((List.range cols).map D) ∧
        ReadsAt rd (ptrAt ihs) hsv) PostQuiet (fs name) fp c e

variable (fs al cert) in
/-- **`LrA` with its end bounded**: every frame at most `F`, within `(q + 4)·(F + 32)` of its cursor. -/
def LrAE (kd : ℕ) (name : String) (cols nhs hbits : ℕ) : Prop :=
  ∀ (q ip irow ihs : ℕ) (mu : E) (D Pos : ℕ → E) (hsv : List E) (R : ℕ → Prop),
    resBatch ≤ q → q < 2 ^ 30 → hsv.length = nhs →
    (∀ i < q, R (ip + i)) → (∀ i < cols, R (irow + i)) → (∀ i < nhs, R (ihs + i)) →
    ∀ fp c, fp + fs name ≤ c → ∃ e, (∀ F, (∀ f, fs f ≤ F) → e ≤ c + (q + 4) * (F + 32)) ∧
      CallAtA fs al cert kd name
      [ptrAt ip, ptrAt irow, ptrAt ihs, mu, gen ^ (q / resBatch), gen ^ (q % resBatch)]
      [(lrPair (lrP cols D) (lrH cols nhs hbits hsv) mu Pos q).1,
        (lrPair (lrP cols D) (lrH cols nhs hbits hsv) mu Pos q).2]
      R (fun _ => False) (fun _ => True)
      (fun rd => ReadsAt rd (ptrAt ip) (posL q Pos) ∧ ReadsAt rd (ptrAt irow) ((List.range cols).map D) ∧
        ReadsAt rd (ptrAt ihs) hsv) PostQuiet (fs name) fp c e

theorem LrAE.toA {kd : ℕ} {name : String} {cols nhs hbits : ℕ} (h : LrAE fs al cert kd name cols nhs hbits) :
    LrA fs al cert kd name cols nhs hbits := by
  intro q ip irow ihs mu D Pos hsv R h1 h2 h3 h4 h5 h6 fp c hfc
  obtain ⟨e, -, he⟩ := h q ip irow ihs mu D Pos hsv R h1 h2 h3 h4 h5 h6 fp c hfc
  exact ⟨e, he⟩

/-- `level_residual`'s end, from its pieces. -/
theorem lr_end_le {c q b r F x : ℕ} (hbr : b + r ≤ q)
    (hx : x ≤ c + 2 * (b + r + 1) + 30 + b * F + F + r * F + F) : x ≤ c + (q + 4) * (F + 32) := by
  have h1 : b * F + r * F ≤ q * F := by rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ hbr
  have h2 : (q + 4) * (F + 32) = q * F + 4 * F + 32 * q + 128 := by ring
  omega

theorem gen_zero_add_ne {n : ℕ} (h1 : 1 ≤ n) (h2 : n < 2 ^ 30) : (gen ^ 0 + gen ^ n : E) ≠ 0 := by
  rw [pow_zero]; exact Whir.one_add_gen_pow_ne h1 h2

theorem gw_gen (n : ℕ) (h : n < 2 ^ 64) : gw n = gen ^ n := Whir.gw_eq (by unfold u128Bound; omega)

/-- **`level_residual` completes placed, its end bounded.** -/
theorem lrAE_complete' {kd : ℕ} {name l1 l2 : String} {cols nhs hbits : ℕ} {fo f1 f2 : Fn}
    (hfo : coreProgram.find? name = some fo) (hpo : fo.params = osParams 6) (hbo : fo.body = lrBody l1 l2)
    (hf1 : coreProgram.find? l1 = some f1) (hp1 : f1.params = osParams 7)
    (hb1 : f1.body = lrLoop1Body cols nhs hbits l1)
    (hf2 : coreProgram.find? l2 = some f2) (hp2 : f2.params = osParams 7)
    (hb2 : f2.body = lrLoop2Body cols nhs hbits l2)
    (hc1 : lr1Checks cols nhs hbits l1 = true) (hc2 : lr2Checks cols nhs hbits l2 = true) :
    LrAE fs al cert kd name cols nhs hbits := by
  intro q ip irow ihs mu D Pos hsv R hq8 hq hlen hRp hRr hRh fp c hfc
  -- the loops' flags and purity
  have hlo : coreProgram.loop name = false := by
    rw [Program.loop_of_find? hfo, Fn.loop, hbo, lrBody_eq]; rfl
  have k1 := hc1
  simp only [lr1Checks, Bool.and_eq_true, decide_eq_true_eq] at k1
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hat1⟩, hok1⟩, -⟩, -⟩, -⟩ := k1
  have k2 := hc2
  simp only [lr2Checks, Bool.and_eq_true, decide_eq_true_eq] at k2
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hat2⟩, hok2⟩, -⟩, -⟩, -⟩ := k2
  have hB1 : f1.body = _ := hb1.trans (lr1_body (name := l1) hat1)
  have hB2 : f2.body = _ := hb2.trans (lr2_body (name := l2) hat2)
  have hS1 : coreProgram.PureIn [l1] := pureIn_loopFlat hf1 hB1 hok1
  have hS2 : coreProgram.PureIn [l2] := pureIn_loopFlat hf2 hB2 hok2
  have hl1 : coreProgram.loop l1 = true := loop_loopFlat hf1 hB1
  have hl2 : coreProgram.loop l2 = true := loop_loopFlat hf2 hB2
  -- the counts
  set b := q / resBatch with hb
  set r := q % resBatch with hr
  have hqbr : resBatch * b + r = q := Nat.div_add_mod q resBatch
  have h8 : resBatch = 8 := rfl
  have hb1' : 1 ≤ b := Nat.div_pos hq8 (by decide)
  have hb30 : b < 2 ^ 30 := lt_of_le_of_lt (Nat.div_le_self _ _) hq
  obtain ⟨PQ, hPQ⟩ : ∃ PQ, PQ = lrPair (lrP cols D) (lrH cols nhs hbits hsv) mu Pos q := ⟨_, rfl⟩
  let σ : Val := lrσ ip irow ihs c mu b r PQ
  set es := (lrPre l1 l2).flatMap (slEvs σ) with hes
  have hw : walk σ fo.body = .ret es [.n 27, .n 28] := by
    rw [hbo, lrBody_eq]; exact walk_straight σ _ _ (lrPre_straight l1 l2)
  have hal : allocs σ es = [2 * (b + r + 1)] := by
    rw [hes, (straight_parts σ _ (lrPre_straight l1 l2)).2.1]
    show [logG (gen ^ (2 * (b + r + 1)))] = _
    rw [gen_pow_eq_ofK, logG_spec (by omega)]
  have hsum : (allocs σ es).sum = 2 * (b + r + 1) := by rw [hal]; simp
  have hcalls := lr_calls σ l1 l2
  rw [← hes] at hcalls
  -- the chain
  let Wo : Words := [(c, lrChainL (lrP cols D) (lrH cols nhs hbits hsv) mu Pos b r)]
  have hRd : ∀ rd, HoldsWords rd Wo →
      ReadsAt rd (ptrAt c) (lrChainL (lrP cols D) (lrH cols nhs hbits hsv) mu Pos b r) :=
    fun rd h => h _ List.mem_cons_self
  have hlenC : (lrChainL (lrP cols D) (lrH cols nhs hbits hsv) mu Pos b r).length = 2 * (b + r + 1) := by
    simp [lrChainL]
  have hown : ∀ i, c ≤ i → i < c + 2 * (b + r + 1) → ownData cert fp c name (allocs σ es) es i := by
    intro i h1 h2
    rw [hal]
    exact ownData_buf (s := 2 * (b + r + 1)) (b := c) (by simp [bases]) h1 h2
  let Rc : ℕ → Prop := fun i => (c ≤ i ∧ i < c + 2 * (b + r + 1)) ∨ R i
  have hRc : ∀ i, Rc i → R i ∨ ownData cert fp c name (allocs σ es) es i := by
    rintro i (⟨h1, h2⟩ | hi)
    · exact Or.inr (hown i h1 h2)
    · exact Or.inl hi
  have hLR : LrRegion q cols nhs ip irow ihs c Rc :=
    ⟨fun i hi => Or.inr (hRp i hi), fun i hi => Or.inr (hRr i hi), fun i hi => Or.inr (hRh i hi),
      fun i hi => Or.inl ⟨by omega, by omega⟩⟩
  -- the batches' loop
  set cur1 := allocBase (al l1) (c + (allocs σ es).sum)
  have hloop1 : ∀ Pre' : Reader → Prop,
      (∀ rd, Pre' rd → LrMem q cols nhs hbits ip irow ihs c mu D Pos hsv rd) →
      CallAtA fs al cert kd l1 (lr1Args 0 b ip c irow ihs mu) [] Rc (fun _ => False) (fun _ => True)
        Pre' PostQuiet (lpB fs l1 b 0) cur1 (cur1 + lpB fs l1 b 0) (cur1 + lpB fs l1 b 0) := by
    intro Pre' hP
    refine callAtA_of_callCompletes0 hS1 (by simp) le_rfl
      ((lr1_loop hf1 hp1 hb1 hc1 hq ip irow ihs c mu D Pos hsv hlen (b - 1) 0 (by omega)).mono hP
        fun _ _ _ h => h) fun rd t _ _ hn hv hbt _ => ?_
    have := lr1_shape (fs := fs) (al := al) hf1 hp1 hb1 hl1 hc1 hq hLR (b - 1) 0 (by omega) rd t hn hv hbt
    exact ⟨this.1, this.2.1 _, this.2.2.1, this.2.2.2⟩
  -- the rest's loop
  set cur2 := allocBase (al l2) (cur1 + lpB fs l1 b 0)
  have hloop2 : 1 ≤ r → ∀ Pre' : Reader → Prop,
      (∀ rd, Pre' rd → LrMem q cols nhs hbits ip irow ihs c mu D Pos hsv rd) →
      CallAtA fs al cert kd l2 (lr2Args 0 r (c + 2 * b) (ip + resBatch * b) irow ihs mu) [] Rc
        (fun _ => False) (fun _ => True) Pre' PostQuiet (lpB fs l2 r 0) cur2 (cur2 + lpB fs l2 r 0)
        (cur2 + lpB fs l2 r 0) := by
    intro hr1 Pre' hP
    refine callAtA_of_callCompletes0 hS2 (by simp) le_rfl
      ((lr2_loop hf2 hp2 hb2 hc2 hq ip irow ihs c mu D Pos hsv hlen (r - 1) 0 (by omega)).mono hP
        fun _ _ _ h => h) fun rd t _ _ hn hv hbt _ => ?_
    have := lr2_shape (fs := fs) (al := al) hf2 hp2 hb2 hl2 hc2 hLR (r - 1) 0 (by omega) rd t hn hv hbt
    exact ⟨this.1, this.2.1 _, this.2.2.1, this.2.2.2⟩
  have hd14 : decide (σ (.n 14) ≠ 0) = true := by
    simp only [decide_eq_true_eq]; exact gen_zero_add_ne hb1' hb30
  have hmem : ∀ rd, ((ReadsAt rd (ptrAt ip) (posL q Pos) ∧ ReadsAt rd (ptrAt irow) ((List.range cols).map D) ∧
      ReadsAt rd (ptrAt ihs) hsv) ∧ HoldsWords rd Wo) → LrMem q cols nhs hbits ip irow ihs c mu D Pos hsv rd :=
    fun rd h => ⟨h.1.1, h.1.2.1, h.1.2.2, hRd rd h.2⟩
  -- the callees
  have hcur1 : cur1 ≤ c + (allocs σ es).sum + 15 := allocBase_le _ _
  have hcur2 : cur2 ≤ cur1 + lpB fs l1 b 0 + 15 := allocBase_le _ _
  have hlp1 : lpB fs l1 b 0 = b * fs l1 + fs (tailKey l1) := by simp [lpB]
  have hlp2 : lpB fs l2 r 0 = r * fs l2 + fs (tailKey l2) := by simp [lpB]
  have hbr : b + r ≤ q := by have := hqbr; rw [h8] at this; omega
  have hkids : ∃ e, (∀ F, (∀ f, fs f ≤ F) → e ≤ c + (q + 4) * (F + 32)) ∧ KidsAtF fs al cert kd σ (fun i => R i ∨ ownData cert fp c name (allocs σ es) es i)
      (fun rd => ReadsAt rd (ptrAt ip) (posL q Pos) ∧ ReadsAt rd (ptrAt irow) ((List.range cols).map D) ∧
        ReadsAt rd (ptrAt ihs) hsv)
      (fun rd => HoldsWords rd Wo) (fun _ => False) ((calls es).map fun _ => PostQuiet) (calls es)
      (c + (allocs σ es).sum) e (fun rd => HoldsWords rd Wo) (fun _ => False) := by
    rw [hcalls]
    simp only [List.map_cons, List.map_nil]
    by_cases hr0 : r = 0
    · have hd23 : decide (σ (.n 23) ≠ 0) = false := by
        simp only [decide_eq_false_iff_not, not_not]
        show gen ^ 0 + gen ^ r = 0
        rw [hr0]; exact CharTwo.add_self_eq_zero _
      refine ⟨cur2 + fs (tailKey l2), fun F hF => lr_end_le hbr (by
        have := Nat.mul_le_mul_left b (hF l1); have := Nat.mul_le_mul_left r (hF l2)
        have := hF (tailKey l1); have := hF (tailKey l2); omega), ?_⟩
      rw [KidsAtF]
      simp only [hd14, ↓reduceIte]
      refine ⟨lpB fs l1 b 0, cur1 + lpB fs l1 b 0, Rc, fun _ => False, fun _ => True,
        fun i hi => Or.inl (hRc i hi), hloop1 _ hmem, ?_⟩
      rw [KidsAtF]
      simp only [hd23, Bool.false_eq_true, ↓reduceIte]
      refine ⟨⟨fun v => ([V.n 24, .n 5, .n 17, .n 21, .n 1, .n 2, .n 3].map σ).getD v.idx 0, f2, hf2, ?_⟩, ?_⟩
      · rw [hp2]; exact params_range_map _
      · rw [KidsAtF]; exact ⟨rfl, fun rd h => h.1, fun i h => h.elim⟩
    · have hd23 : decide (σ (.n 23) ≠ 0) = true := by
        simp only [decide_eq_true_eq]; exact gen_zero_add_ne (by omega) (by omega)
      refine ⟨cur2 + lpB fs l2 r 0, fun F hF => lr_end_le hbr (by
        have := Nat.mul_le_mul_left b (hF l1); have := Nat.mul_le_mul_left r (hF l2)
        have := hF (tailKey l1); have := hF (tailKey l2); omega), ?_⟩
      rw [KidsAtF]
      simp only [hd14, ↓reduceIte]
      refine ⟨lpB fs l1 b 0, cur1 + lpB fs l1 b 0, Rc, fun _ => False, fun _ => True,
        fun i hi => Or.inl (hRc i hi), hloop1 _ hmem, ?_⟩
      rw [KidsAtF]
      simp only [hd23, ↓reduceIte]
      refine ⟨lpB fs l2 r 0, cur2 + lpB fs l2 r 0, Rc, fun _ => False, fun _ => True,
        fun i hi => Or.inl (hRc i hi), hloop2 (by omega) _ fun rd h => hmem rd ⟨h.1, h.2.1⟩, ?_⟩
      rw [KidsAtF]; exact ⟨rfl, fun rd h => h.1.1, fun i h => h.elim⟩
  obtain ⟨e, hbe, hk⟩ := hkids
  have hlA : loadAddrs σ es = [(σ (.n 10)).limb 0 * addressOfIndex 0, (σ (.n 10)).limb 0 * addressOfIndex 1,
      (σ (.n 26)).limb 0 * addressOfIndex 0, (σ (.n 26)).limb 0 * addressOfIndex 1] := by
    rw [loadAddrs, hes, filterMap_slEvs (Ev.loadAddr? σ) σ (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)]
    rfl
  have hhA : heapHintAddrs σ es = [] := by
    rw [heapHintAddrs, hes, flatMap_slEvs (Ev.hintAddrs σ) σ (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)]
    rfl
  refine ⟨e, hbe, callAtA_node hlo hfc ⟨σ, fo, es, [.n 27, .n 28], Wo, (calls es).map fun _ => PostQuiet,
    fun rd => HoldsWords rd Wo, fun _ => False, hfo, by rw [hpo]; rfl, hw, by show [PQ.1, PQ.2] = _; rw [hPQ],
    ?_, ?_, ?_, ?_, fun _ h => h.elim, hk, fun _ _ => trivial, ?_, ?_⟩⟩
  · -- placed
    rw [hal]
    refine ⟨?_, fun q' hq' => ?_⟩
    · rw [hes, (straight_parts σ _ (lrPre_straight l1 l2)).1]; rfl
    · have h0 : (lrPre l1 l2).filterMap Stmt.addrS = [] := rfl
      rw [hes, (straight_parts σ _ (lrPre_straight l1 l2)).2.2.1, h0] at hq'
      exact absurd hq' List.not_mem_nil
  · -- own words
    rw [hsum]
    refine ⟨fun q' hq' => Or.inr ?_, List.pairwise_singleton _ _⟩
    simp only [Wo, List.mem_cons, List.not_mem_nil, or_false] at hq'
    subst hq'
    exact ⟨le_rfl, by simp [hlenC]⟩
  · -- loads
    intro A hA
    rw [hlA] at hA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
    have s10 : σ (.n 10) = ptrAt c := rfl
    have s26 : σ (.n 26) = ptrAt (c + 2 * b + 2 * r) := rfl
    rcases hA with rfl | rfl | rfl | rfl <;> simp only [s10, s26, Main.addr_ofK] <;>
      exact ⟨_, rfl, Or.inl (hown _ (by omega) (by omega))⟩
  · -- heap hints
    intro A hA
    rw [hhA] at hA
    exact absurd hA List.not_mem_nil
  · -- the events
    intro rd _ _ hW
    have hch := hRd rd hW
    obtain ⟨z0, z1⟩ := lrChain_load hch (i := 0) (by omega)
    have hp0 : lrPair (lrP cols D) (lrH cols nhs hbits hsv) mu Pos (lrCnt b 0) = (0, 0) := by
      simp [lrCnt, lrPair, resFold]
    rw [hp0] at z0 z1
    obtain ⟨w0, w1⟩ := lrChain_load hch (i := b + r) le_rfl
    rw [lrCnt_rest, hqbr, ← hPQ] at w0 w1
    have e26 : c + 2 * b + 2 * r = c + 2 * (b + r) := by ring
    refine holds_slEvs _ (fun a ha => ?_) (fun c' f args h => ?_)
    · simp only [lrPre, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq, reduceCtorEq,
        false_or] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · show gen ^ (b + r) = gen ^ b * gen ^ r; exact pow_add _ _ _
      · show gen ^ 1 = gw 1; exact (gw_gen 1 (by norm_num)).symm
      · show gen ^ (b + r + 1) = gen ^ (b + r) * gen ^ 1; exact pow_add _ _ _
      · show gen ^ (2 * (b + r + 1)) = gen ^ (b + r + 1) * gen ^ (b + r + 1); rw [two_mul, pow_add]
      · trivial
      · show (0 : E) = word 0 0; exact word_zero.symm
      · show LoadHolds rd (ptrAt c) 0 0; simpa using z0
      · show (0 : E) = word 0 0; exact word_zero.symm
      · show LoadHolds rd (ptrAt c) 1 0; simpa using z1
      · show gen ^ 0 = gw 0; exact (gw_gen 0 (by norm_num)).symm
      · rfl
      · show gen ^ 0 = gw 0; exact (gw_gen 0 (by norm_num)).symm
      · show gen ^ (2 * b) = gen ^ b * gen ^ b; rw [two_mul, pow_add]
      · show ptrAt (c + 2 * b) = ptrAt c * gen ^ (2 * b); exact (ptrAt_mul_gen c (2 * b)).symm
      · show gen ^ (2 * b) = gen ^ b * gen ^ b; rw [two_mul, pow_add]
      · show gen ^ (4 * b) = gen ^ (2 * b) * gen ^ (2 * b); rw [← pow_add]; congr 1; ring
      · show gen ^ (resBatch * b) = gen ^ (4 * b) * gen ^ (4 * b); rw [← pow_add, h8]; congr 1; ring
      · show ptrAt (ip + resBatch * b) = ptrAt ip * gen ^ (resBatch * b)
        exact (ptrAt_mul_gen ip (resBatch * b)).symm
      · show gen ^ 0 = gw 0; exact (gw_gen 0 (by norm_num)).symm
      · rfl
      · show gen ^ 0 = gw 0; exact (gw_gen 0 (by norm_num)).symm
      · show gen ^ (2 * r) = gen ^ r * gen ^ r; rw [two_mul, pow_add]
      · show ptrAt (c + 2 * b + 2 * r) = ptrAt (c + 2 * b) * gen ^ (2 * r)
        exact (ptrAt_mul_gen (c + 2 * b) (2 * r)).symm
      · show LoadHolds rd (ptrAt (c + 2 * b + 2 * r)) 0 PQ.1
        rw [e26, loadHolds_ptrAt_add, Nat.add_zero]; exact w0
      · show LoadHolds rd (ptrAt (c + 2 * b + 2 * r)) 1 PQ.2
        rw [e26, loadHolds_ptrAt_add]; exact w1
    · simp only [lrPre, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
        Stmt.callIf.injEq] at h
      rcases h with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩
      · exact isInK_add (gen_pow_isInK 0) (gen_pow_isInK b)
      · exact isInK_add (gen_pow_isInK 0) (gen_pow_isInK r)
  · -- the post
    intro rd ts _ _ _ hv hq'
    refine postQuiet_node hfo hw (fun a ha => ?_) (fun ev hev => ?_) hv hq' _
    · have := List.all_eq_true.mp (lr_quiet l1 l2) _ (mem_atom_slEvs ha)
      simpa using this
    · cases ev with
      | atom a =>
        refine exact_of_trivExact ?_
        have := List.all_eq_true.mp (lr_triv l1 l2) _ (mem_atom_slEvs hev)
        simpa using this
      | _ => trivial

/-! ## Every specialization -/

/-- **`level_residual` completes placed.** -/
theorem lrA_complete' {kd : ℕ} {name l1 l2 : String} {cols nhs hbits : ℕ} {fo f1 f2 : Fn}
    (hfo : coreProgram.find? name = some fo) (hpo : fo.params = osParams 6) (hbo : fo.body = lrBody l1 l2)
    (hf1 : coreProgram.find? l1 = some f1) (hp1 : f1.params = osParams 7)
    (hb1 : f1.body = lrLoop1Body cols nhs hbits l1)
    (hf2 : coreProgram.find? l2 = some f2) (hp2 : f2.params = osParams 7)
    (hb2 : f2.body = lrLoop2Body cols nhs hbits l2)
    (hc1 : lr1Checks cols nhs hbits l1 = true) (hc2 : lr2Checks cols nhs hbits l2 = true) :
    LrA fs al cert kd name cols nhs hbits :=
  (lrAE_complete' hfo hpo hbo hf1 hp1 hb1 hf2 hp2 hb2 hc1 hc2).toA

/-- **Every `level_residual` completes placed, its end bounded.** -/
theorem lrAE_complete (kd : ℕ) : ∀ e ∈ lrTable, LrAE fs al cert kd e.1 e.2.1 e.2.2.1 e.2.2.2.1 := by
  intro e he
  obtain ⟨⟨fo, hfo, hpo, hbo⟩, ⟨f1, hf1, hp1, hb1⟩, ⟨f2, hf2, hp2, hb2⟩⟩ := lrTable_ok e he
  obtain ⟨hc1, hc2⟩ := lr_checks e he
  exact lrAE_complete' hfo hpo hbo hf1 hp1 hb1 hf2 hp2 hb2 hc1 hc2

/-- **Every `level_residual` completes placed.** -/
theorem lrA_complete (kd : ℕ) : ∀ e ∈ lrTable, LrA fs al cert kd e.1 e.2.1 e.2.2.1 e.2.2.2.1 :=
  fun e he => (lrAE_complete kd e he).toA

end
end LeanVM.Guest.B1.VsC
