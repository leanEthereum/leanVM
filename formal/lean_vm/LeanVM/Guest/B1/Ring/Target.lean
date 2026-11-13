/-
  LeanVM.Guest.B1.Ring.Target

  B1 of `ring_switch_target`: its core IR computes the statement's `ringTarget`.
-/

module

public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.B1.Ring.Interface
public import LeanVM.Guest.B1.Ring.TargetMath
public import LeanVM.Guest.B1.KeccakGkr.Lib
public import LeanVM.Guest.B1.Common.Find
public import LeanVM.Guest.Data.NameStrings

/-!
# `ring_switch_target` (TRIAGE G #64, #65)

`ring_switch_target(slices, map_challenges)` (`fn% «ring_switch_target»`) zeroes the eight Horner chains'
first row of `rs_chain` and runs `ring_switch_target_loop0` (`fn% «ring_switch_target_loop0»`) for `x = g^j`, `j < 8`. The loop
body reads `g_0 .. g_7` (`map_challenges[8 ..]`), computes `Ψ` (`ring_psi`, inline: `psRow`) of
the eight slices at `slices·x^8`, and steps each chain `p` by eight Horner steps in
`w_p = RING_W[p]` (`hzRow`), from row `x^8` of `rs_chain` to the next. Chain `p` ends at
`wHorner w_p (Ψ(s_0), …, Ψ(s_63))`; the tail raises it to `2^(8p)` by `8p` squarings, scales it by
`f_p = map_challenges[p]`, sums, and multiplies by `x^63`: `guest_target_eq`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## `ring_psi` on one row -/

/-- Row `r`'s first value. -/
abbrev psBase (r : ℕ) : ℕ := 16 + 23 * r

/-- Stage `k + 2` of `Ψ` on the row at `b`: square, scale by `g_(k+2)`, add. -/
def psStage (b k : ℕ) : List Stmt :=
  [.atom (.mul (.n (b + 5 + 3 * k)) (.n (b + 2 + 3 * k)) (.n (b + 2 + 3 * k))),
    .atom (.mul (.n (b + 6 + 3 * k)) (.n (6 + k)) (.n (b + 5 + 3 * k))),
    .atom (.add (.n (b + 7 + 3 * k)) (.n (b + 4 + 3 * k)) (.n (b + 6 + 3 * k)))]

/-- The row of slice `r`, its values from `b`: `Ψ` of `rows[r]` at `b + 22`. -/
def psRowAt (b r : ℕ) : List Stmt :=
  [.atom (.load (.n b) (.n 15) r), .atom (.mul (.n (b + 1)) (.n 4) (.n b)),
    .atom (.mul (.n (b + 2)) (.n b) (.n b)), .atom (.mul (.n (b + 3)) (.n 5) (.n (b + 2))),
    .atom (.add (.n (b + 4)) (.n (b + 1)) (.n (b + 3)))] ++
  ((List.range 6).map (psStage b)).flatten

/-- Row `r`. -/
def psRow (r : ℕ) : List Stmt := psRowAt (psBase r) r

theorem psStage_noRet (b k : ℕ) : Stmt.noRetList (psStage b k) = true := rfl

theorem psRow_noRet (r : ℕ) : Stmt.noRetList (psRow r) = true := by
  rw [psRow, psRowAt, noRetList_append, noRetList_flatten_map _ (psStage_noRet _) _]; rfl

/-- The challenges `g_0 .. g_7`, at `4 .. 11`. -/
def gVals (σ : Val) : List E := (List.range 8).map fun b ↦ σ (.n (4 + b))

/-- **One row of `ring_psi`**: the slice it loads, and `Ψ` of it at `b + 22`. -/
theorem holds_psRowAt {b r : ℕ} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (psRowAt b r) True kret) :
    LoadHolds rd (σ (.n 15)) r (σ (.n b)) ∧ σ (.n (b + 22)) = ringPsi (σ (.n b)) (gVals σ) := by
  rw [psRowAt, holdsList_append] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨l0, e1, e2, e3, e4, h⟩ := h
  obtain ⟨hs, -⟩ := (holdsList_range_flatten 6 (psStage b) (psStage_noRet b) _ _).mp h
  have st : ∀ k < 6, σ (.n (b + 5 + 3 * k)) = σ (.n (b + 2 + 3 * k)) * σ (.n (b + 2 + 3 * k)) ∧
      σ (.n (b + 6 + 3 * k)) = σ (.n (6 + k)) * σ (.n (b + 5 + 3 * k)) ∧
      σ (.n (b + 7 + 3 * k)) = σ (.n (b + 4 + 3 * k)) + σ (.n (b + 6 + 3 * k)) := by
    intro k hk
    have := hs k hk
    simp only [psStage, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at this
    exact ⟨this.1, this.2.1, this.2.2.1⟩
  obtain ⟨a0, b0, c0⟩ := st 0 (by decide)
  obtain ⟨a1, b1, c1⟩ := st 1 (by decide)
  obtain ⟨a2, b2, c2⟩ := st 2 (by decide)
  obtain ⟨a3, b3, c3⟩ := st 3 (by decide)
  obtain ⟨a4, b4, c4⟩ := st 4 (by decide)
  obtain ⟨a5, b5, c5⟩ := st 5 (by decide)
  simp only [Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul] at a0 b0 c0 a1 b1 c1 a2 b2 c2
  simp only [Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul] at a3 b3 c3 a4 b4 c4 a5 b5 c5
  refine ⟨l0, ?_⟩
  simp only [gVals, List.range_succ, List.range_zero, List.map_nil, List.map_cons,
    List.nil_append, List.cons_append, ringPsi, List.foldl_cons, List.foldl_nil, Nat.reduceAdd]
  rw [c5, b5, a5, c4, b4, a4, c3, b3, a3, c2, b2, a2, c1, b1, a1, c0, b0, a0, e4, e3, e2, e1]
  ring

/-! ## The Horner chains -/

/-- `RING_W[p]`'s words: `w_p = z_p⁻¹`, `z_p = x^(2^(64 - 8p))` (`ringWK`). -/
def ringWNat : List ℕ :=
  [9223372036854775821, 3553348109046704045, 6991530515271458276, 8630512066575425152,
    8543422393626980591, 2539607212871081783, 4576227429734584387, 15746294976420764300]

theorem word_ringW {p : ℕ} (hp : p < 8) : word (ringWNat.getD p 0) 0 = ofK (ringWK.getD p 0) := by
  rw [word_eOfNat]
  interval_cases p <;> rfl

/-- Chain `p`'s first value. -/
abbrev hzBase (p : ℕ) : ℕ := 204 + 25 * p

/-- Step `r` of chain `p` (values from `a`): `acc·w_p + Ψ(s_r)`. -/
def hzStep (a p r : ℕ) : List Stmt :=
  [.atom (.const (.n (a + 1 + 3 * r)) (word (ringWNat.getD p 0) 0)),
    .atom (.mul (.n (a + 2 + 3 * r)) (.n (a + 3 * r)) (.n (a + 1 + 3 * r))),
    .atom (.add (.n (a + 3 + 3 * r)) (.n (a + 2 + 3 * r)) (.n (psBase r + 22)))]

/-- Chain `p` over one chunk, its values from `a`: its row's entry `p` in, entry `8 + p` out. -/
def hzRowAt (a p : ℕ) : List Stmt :=
  [.atom (.load (.n a) (.n 203) p)] ++ ((List.range 8).map (hzStep a p)).flatten ++
    [.atom (.load (.n (a + 24)) (.n 203) (8 + p))]

/-- Chain `p`. -/
def hzRow (p : ℕ) : List Stmt := hzRowAt (hzBase p) p

theorem hzStep_noRet (a p r : ℕ) : Stmt.noRetList (hzStep a p r) = true := rfl

theorem hzRow_noRet (p : ℕ) : Stmt.noRetList (hzRow p) = true := by
  rw [hzRow, hzRowAt, noRetList_append, noRetList_append,
    noRetList_flatten_map _ (hzStep_noRet _ _) _]; rfl

/-- The eight images `Ψ(s_r)` of a chunk. -/
def psVals (σ : Val) : List E := (List.range 8).map fun r ↦ σ (.n (psBase r + 22))

/-- One Horner step in `w`. -/
def hstep (w : E) (acc c : E) : E := acc * w + c

theorem hz_steps {a p : ℕ} (hp : p < 8)
    (hs : ∀ r < 8, σ (.n (a + 1 + 3 * r)) = word (ringWNat.getD p 0) 0 ∧
      σ (.n (a + 2 + 3 * r)) = σ (.n (a + 3 * r)) * σ (.n (a + 1 + 3 * r)) ∧
      σ (.n (a + 3 + 3 * r)) = σ (.n (a + 2 + 3 * r)) + σ (.n (psBase r + 22))) :
    ∀ r ≤ 8, σ (.n (a + 3 * r)) =
      (((List.range r).map fun t ↦ σ (.n (psBase t + 22))).foldl
        (hstep (ofK (ringWK.getD p 0))) (σ (.n a)))
  | 0, _ => by simp
  | r + 1, hr => by
    obtain ⟨e1, e2, e3⟩ := hs r (by omega)
    rw [show a + 3 * (r + 1) = a + 3 + 3 * r by ring, e3, e2, e1, word_ringW hp,
      hz_steps hp hs r (by omega), List.range_succ, List.map_append, List.foldl_append]
    rfl

/-- **One chain over one chunk.** -/
theorem holds_hzRowAt {a p : ℕ} (hp : p < 8) {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (hzRowAt a p) True kret) :
    LoadHolds rd (σ (.n 203)) p (σ (.n a)) ∧
      LoadHolds rd (σ (.n 203)) (8 + p)
        ((psVals σ).foldl (hstep (ofK (ringWK.getD p 0))) (σ (.n a))) := by
  rw [hzRowAt, holdsList_append, holdsList_append] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨l0, h⟩ := h
  obtain ⟨hs, l24, -⟩ := (holdsList_range_flatten 8 (hzStep a p) (hzStep_noRet a p) _ _).mp h
  have hs' : ∀ r < 8, σ (.n (a + 1 + 3 * r)) = word (ringWNat.getD p 0) 0 ∧
      σ (.n (a + 2 + 3 * r)) = σ (.n (a + 3 * r)) * σ (.n (a + 1 + 3 * r)) ∧
      σ (.n (a + 3 + 3 * r)) = σ (.n (a + 2 + 3 * r)) + σ (.n (psBase r + 22)) := by
    intro r hr
    have := hs r hr
    simp only [hzStep, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at this
    exact ⟨this.1, this.2.1, this.2.2.1⟩
  refine ⟨l0, ?_⟩
  have := hz_steps hp hs' 8 le_rfl
  rw [show a + 3 * 8 = a + 24 by ring] at this
  rw [psVals, ← this]
  exact l24

/-! ## The loop body (`ring_switch_target_loop0`) -/

/-- `ring_switch_target_loop0`'s body. -/
def loop13T : List Stmt :=
  ((List.range 8).map fun b ↦ [.atom (.load (.n (4 + b)) (.n 1) (8 + b))]).flatten ++
  [.atom (.mul (.n 12) (.n 0) (.n 0)), .atom (.mul (.n 13) (.n 12) (.n 12)),
    .atom (.mul (.n 14) (.n 13) (.n 13)), .atom (.mul (.n 15) (.n 2) (.n 14))] ++
  ((List.range 8).map psRow).flatten ++
  [.atom (.mul (.n 200) (.n 0) (.n 0)), .atom (.mul (.n 201) (.n 200) (.n 200)),
    .atom (.mul (.n 202) (.n 201) (.n 201)), .atom (.mul (.n 203) (.n 3) (.n 202))] ++
  ((List.range 8).map hzRow).flatten ++
  [.atom (.const (.n 404) (word 2 0)), .atom (.mul (.n 405) (.n 0) (.n 404)),
    .atom (.const (.n 406) (word 256 0)), .atom (.add (.n 407) (.n 405) (.n 406)),
    .atom (.const (.n 408) (word 2 0)), .atom (.mul (.n 409) (.n 0) (.n 408)),
    .callIf (.n 407) name% «ring_switch_target_loop0» [.n 409, .n 1, .n 2, .n 3], .ret []]

theorem loop13_body : (fn% «ring_switch_target_loop0»).body = loop13T := stmtsEqb_sound (by decide +kernel)

theorem find_loop13 : coreProgram.find? name% «ring_switch_target_loop0» = some fn% «ring_switch_target_loop0» :=
  coreProgram_find?_at (j := idx% «ring_switch_target_loop0») rfl

/-- **The loop body's meaning at `x`**: `g_0 .. g_7` at `map_challenges[8 ..]`, the eight slices
at `slices·x^8`, and each chain `p`'s entry `p` of row `rs_chain·x^8` stepped by the chunk's images
into its entry `8 + p`. -/
def RowOk13 (rd : Reader) (mc sl ch x : E) : Prop :=
  ∃ gs vs : List E, gs.length = 8 ∧ vs.length = 8 ∧ (∀ b < 8, LoadHolds rd mc (8 + b)
      (gs.getD b 0)) ∧ ReadsAt rd (sl * x ^ 8) vs ∧
    ∀ p < 8, ∃ acc : E, LoadHolds rd (ch * x ^ 8) p acc ∧
      LoadHolds rd (ch * x ^ 8) (8 + p)
        ((vs.map (ringPsi · gs)).foldl (hstep (ofK (ringWK.getD p 0))) acc)

/-- **`ring_switch_target_loop0`'s step**: at depth `d + 1` and `x`, the body's meaning, and the call at `x·g`
one level shallower unless `x·g = g^8`. -/
theorem loop13_step (d : ℕ) (x mc sl ch : E)
    (h : coreProgram.relN rd (d + 1) name% «ring_switch_target_loop0» [x, mc, sl, ch] []) :
    RowOk13 rd mc sl ch x ∧
      (x * gen + gen ^ 8 ≠ 0 → coreProgram.relN rd d name% «ring_switch_target_loop0» [x * gen, mc, sl, ch] []) := by
  obtain ⟨fn, hf, σ, hpar, hb⟩ := h
  rw [find_loop13] at hf
  cases hf
  rw [loop13_body] at hb
  simp only [core_eq% «ring_switch_target_loop0», List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar hb
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hpar
  simp only [loop13T, holdsList_append] at hb
  obtain ⟨hg, hb⟩ := (holdsList_range_flatten 8
    (fun b ↦ [Stmt.atom (.load (.n (4 + b)) (.n 1) (8 + b))]) (fun _ ↦ rfl) _ _).mp hb
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hb
  obtain ⟨e12, e13, e14, e15, hb⟩ := hb
  obtain ⟨hps, hb⟩ := (holdsList_range_flatten 8 psRow psRow_noRet _ _).mp hb
  obtain ⟨e200, e201, e202, e203, hb⟩ := hb
  obtain ⟨hhz, hb⟩ := (holdsList_range_flatten 8 hzRow hzRow_noRet _ _).mp hb
  obtain ⟨e404, e405, e406, e407, e408, e409, -, hcall, -⟩ := hb
  have hx8 : σ (.n 14) = σ (.n 0) ^ 8 := by rw [e14, e13, e12]; ring
  have hy8 : σ (.n 202) = σ (.n 0) ^ 8 := by rw [e202, e201, e200]; ring
  have hrow : ∀ r < 8, LoadHolds rd (σ (.n 15)) r (σ (.n (psBase r))) ∧
      σ (.n (psBase r + 22)) = ringPsi (σ (.n (psBase r))) (gVals σ) := fun r hr ↦
    holds_psRowAt (hps r hr)
  have hvals : psVals σ = ((List.range 8).map fun r ↦ σ (.n (psBase r))).map
      (ringPsi · (gVals σ)) := by
    simp only [psVals, List.map_map]
    refine List.map_congr_left fun r hr ↦ ?_
    exact (hrow r (List.mem_range.mp hr)).2
  refine ⟨⟨gVals σ, (List.range 8).map fun r ↦ σ (.n (psBase r)), by simp [gVals], by simp,
    fun b hb ↦ ?_, fun r hr ↦ ?_, fun p hp ↦ ?_⟩, ?_⟩
  · have := hg b hb
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at this
    rw [show (gVals σ).getD b 0 = σ (.n (4 + b)) by
      simp [gVals, List.getD_eq_getElem?_getD, hb]]
    exact this.1
  · simp only [List.length_map, List.length_range] at hr
    simp only [List.getElem_map, List.getElem_range]
    rw [← hx8, ← e15]
    exact (hrow r hr).1
  · obtain ⟨l0, l1⟩ := holds_hzRowAt hp (hhz p hp)
    refine ⟨σ (.n (hzBase p)), ?_, ?_⟩
    · rw [← hy8, ← e203]; exact l0
    · rw [← hy8, ← e203, ← hvals]; exact l1
  · intro hne
    have e : σ (.n 407) = σ (.n 0) * gen + gen ^ 8 := by
      rw [e407, e405, e404, e406, word_gen, ← word_two_pow (by decide : 8 < 64)]; rfl
    have e' : σ (.n 409) = σ (.n 0) * gen := by rw [e409, e408, word_gen]
    have := hcall (by rw [e]; exact hne)
    simpa [e'] using this


/-! ## `ring_switch_target` -/

/-- `n` squarings of the value at `h`, into `h + 1 .. h + n`. -/
def sqRunT (h n : ℕ) : List Stmt :=
  ((List.range n).map fun j ↦ [Stmt.atom (.mul (.n (h + j + 1)) (.n (h + j)) (.n (h + j)))]).flatten

theorem holds_sqRunT {h n : ℕ} {kret : List E → Prop}
    (hb : Stmt.HoldsList C rd σ (sqRunT h n) True kret) :
    ∀ j ≤ n, σ (.n (h + j)) = σ (.n h) ^ 2 ^ j := by
  obtain ⟨hs, -⟩ := (holdsList_range_flatten n _ (fun _ ↦ rfl) _ _).mp hb
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    have := hs j (by omega)
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at this
    rw [← Nat.add_assoc, this.1, ih (by omega), ← pow_two, ← pow_mul, ← pow_succ]

/-- Tail block `p`'s first value. -/
abbrev tbBase (p : ℕ) : ℕ := 13 + 4 * p * p

/-- The running sum before tail block `p`. -/
def tbPrev (p : ℕ) : ℕ := if p = 1 then 16 else tbBase (p - 1) + 8 * (p - 1) + 3

/-- Tail block `p ≥ 1`: `sums[p]^(2^(8p))·f_p` added to the running sum. -/
def tbBlock (p : ℕ) : List Stmt :=
  [.atom (.load (.n (tbBase p)) (.n 13) p)] ++ sqRunT (tbBase p) (8 * p) ++
  [.atom (.load (.n (tbBase p + 8 * p + 1)) (.n 1) p),
    .atom (.mul (.n (tbBase p + 8 * p + 2)) (.n (tbBase p + 8 * p + 1)) (.n (tbBase p + 8 * p))),
    .atom (.add (.n (tbBase p + 8 * p + 3)) (.n (tbPrev p)) (.n (tbBase p + 8 * p + 2)))]

theorem tbBlock_noRet (p : ℕ) : Stmt.noRetList (tbBlock p) = true := by
  rw [tbBlock, noRetList_append, noRetList_append, sqRunT,
    noRetList_flatten_map _ (fun _ ↦ rfl) _]; rfl

theorem holds_tbBlock {p : ℕ} {kret : List E → Prop}
    (hb : Stmt.HoldsList C rd σ (tbBlock p) True kret) :
    LoadHolds rd (σ (.n 13)) p (σ (.n (tbBase p))) ∧
      LoadHolds rd (σ (.n 1)) p (σ (.n (tbBase p + 8 * p + 1))) ∧
      σ (.n (tbBase p + 8 * p + 3)) = σ (.n (tbPrev p)) +
        σ (.n (tbBase p + 8 * p + 1)) * σ (.n (tbBase p)) ^ 2 ^ (8 * p) := by
  rw [tbBlock, holdsList_append, holdsList_append] at hb
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hb
  obtain ⟨l0, hb⟩ := hb
  rw [holdsList_noRet _ (by rw [sqRunT]; exact noRetList_flatten_map _ (fun _ ↦ rfl) _)] at hb
  obtain ⟨hs, l1, e2, e3, -⟩ := hb
  refine ⟨l0, l1, ?_⟩
  rw [e3, e2, holds_sqRunT hs (8 * p) le_rfl]

/-- `ring_switch_target`'s body. -/
def rstT : List Stmt :=
  [.atom (.hint (.alloc (.n 2) 72))] ++
  ((List.range 8).map fun p ↦
    [Stmt.atom (.const (.n (3 + p)) (word 0 0)), .atom (.load (.n (3 + p)) (.n 2) p)]).flatten ++
  [.atom (.const (.n 11) (word 1 0)), .call name% «ring_switch_target_loop0» [.n 11, .n 1, .n 0, .n 2] [],
    .atom (.const (.n 12) (word 27 0)), .atom (.mul (.n 13) (.n 2) (.n 12)),
    .atom (.load (.n 14) (.n 1) 0), .atom (.load (.n 15) (.n 13) 0),
    .atom (.mul (.n 16) (.n 14) (.n 15))] ++
  ((List.range 7).map fun p ↦ tbBlock (p + 1)).flatten ++
  [.atom (.const (.n 269) (word 9223372036854775808 0)), .atom (.mul (.n 270) (.n 268) (.n 269)),
    .ret [.n 270]]

theorem rst_body : (fn% «ring_switch_target»).body = rstT := stmtsEqb_sound (by decide +kernel)

theorem find_rst : coreProgram.find? "ring_switch_target" = some fn% «ring_switch_target» :=
  coreProgram_find?_at (j := idx% «ring_switch_target») rfl


theorem word_27 : word 27 0 = gen ^ 64 := by
  rw [word_eOfNat, gen_pow_eq_ofK]
  exact congrArg ofK (by decide +kernel)

theorem gen_eq_genE : gen = Ring.genE := rfl

theorem hstep_foldl_eq (w : E) (l : List E) (a : E) :
    l.foldl (hstep w) a = l.foldl (fun acc c ↦ acc * w + c) a := rfl

/-- **`ring_switch_target` computes the statement's `ringTarget`.** -/
theorem ring_switch_target_holds : ring_switch_target_Spec := by
  intro rd args rets h
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_rst args rets).mp h
  rw [rst_body] at hb
  simp only [core_eq% «ring_switch_target», List.map_cons, List.map_nil] at hpar hb
  subst hpar
  simp only [rstT, holdsList_append] at hb
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hb
  obtain ⟨-, hb⟩ := hb
  obtain ⟨hz, hb⟩ := (holdsList_range_flatten 8 (fun p ↦
    [Stmt.atom (.const (.n (3 + p)) (word 0 0)), .atom (.load (.n (3 + p)) (.n 2) p)])
    (fun _ ↦ rfl) _ _).mp hb
  obtain ⟨e11, hloop, e12, e13, l14, l15, e16, hb⟩ := hb
  obtain ⟨htb, e269, e270, hret⟩ := (holdsList_range_flatten 7 (fun p ↦ tbBlock (p + 1))
    (fun p ↦ tbBlock_noRet (p + 1)) _ _).mp hb
  -- the loop's rows
  have hrows : ∀ j, j < 8 → RowOk13 rd (σ (.n 1)) (σ (.n 0)) (σ (.n 2)) (gen ^ j) := by
    have := loop_sound (P := coreProgram) (f := name% «ring_switch_target_loop0») (ps := [σ (.n 1), σ (.n 0), σ (.n 2)])
      (N := gen ^ 8) (m := 8) (B := RowOk13 rd (σ (.n 1)) (σ (.n 0)) (σ (.n 2)))
      (fun d x h => loop13_step d x _ _ _ h) rfl (by decide) 0
      (by rw [pow_zero, ← word_one, ← e11]; exact hloop)
    exact fun j hj => this j (Nat.zero_le j) hj
  choose gs vs hgl hvl hg hvs hch using hrows
  set G := gs 0 (by decide) with hG
  have hgsame : ∀ j (hj : j < 8), gs j hj = G := by
    intro j hj
    apply List.ext_getElem (by rw [hgl, hgl])
    intro b h1 h2
    have hb8 : b < 8 := by rw [hgl] at h1; exact h1
    have a := hg j hj b hb8
    have c := hg 0 (by decide) b hb8
    rw [List.getD_eq_getElem _ _ h1] at a
    rw [List.getD_eq_getElem _ _ h2] at c
    exact loadHolds_unique a c
  let sF : ℕ → E := fun t ↦ if h : t / 8 < 8 then (vs (t / 8) h).getD (t % 8) 0 else 0
  let img : ℕ → E := fun t ↦ ringPsi (sF t) G
  -- the chains
  have hchain : ∀ j ≤ 8, ∀ p < 8, LoadHolds rd (σ (.n 2)) (8 * j + p)
      (((List.range (8 * j)).map img).foldl (hstep (ofK (ringWK.getD p 0))) 0) := by
    intro j
    induction j with
    | zero =>
      intro _ p hp
      have := hz p hp
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at this
      obtain ⟨ec, lc, -⟩ := this
      rw [ec, word_zero] at lc
      simpa using lc
    | succ j ih =>
      intro hj p hp
      have hj8 : j < 8 := by omega
      obtain ⟨acc, la, lb⟩ := hch j hj8 p hp
      rw [← pow_mul, loadHolds_mul_gen_pow, Nat.mul_comm j 8] at la lb
      have ihp := ih (by omega) p hp
      rw [loadHolds_unique la ihp] at lb
      rw [show 8 * (j + 1) + p = 8 * j + (8 + p) by ring]
      convert lb using 1
      rw [show 8 * (j + 1) = 8 * j + 8 by ring, List.range_add, List.map_append, List.foldl_append,
        hgsame j hj8]
      congr 1
      apply List.ext_getElem (by simp [hvl])
      intro i h1 h2
      simp only [List.length_map, List.length_range] at h1
      simp only [List.getElem_map, List.getElem_range, img, sF]
      have hd : (8 * j + i) / 8 = j := by omega
      have hm : (8 * j + i) % 8 = i := by omega
      simp only [hd, hm, hj8, ↓reduceDIte]
      rw [List.getD_eq_getElem _ _ (by rw [hvl]; exact h1)]
  -- the sums, at `rs_chain·g^64`
  have hsum : ∀ p < 8, LoadHolds rd (σ (.n 13)) p
      (((List.range 64).map img).foldl (hstep (ofK (ringWK.getD p 0))) 0) := by
    intro p hp
    rw [e13, e12, word_27, loadHolds_mul_gen_pow]
    exact hchain 8 le_rfl p hp
  -- the challenges `f_p`
  let fV : ℕ → E := fun p ↦ if p = 0 then σ (.n 14) else σ (.n (tbBase p + 8 * p + 1))
  have hf : ∀ p < 8, LoadHolds rd (σ (.n 1)) p (fV p) := by
    intro p hp
    by_cases h0 : p = 0
    · subst h0; exact l14
    · have := (holds_tbBlock (htb (p - 1) (by omega))).2.1
      rw [show p - 1 + 1 = p by omega] at this
      simpa [fV, h0] using this
  -- the running sum
  let H : ℕ → E := fun p ↦ ((List.range 64).map img).foldl (hstep (ofK (ringWK.getD p 0))) 0
  have hrun : ∀ q < 8, σ (.n (if q = 0 then 16 else tbBase q + 8 * q + 3)) =
      ∑ p ∈ Finset.range (q + 1), fV p * H p ^ 2 ^ (8 * p) := by
    intro q
    induction q with
    | zero =>
      intro _
      simp only [↓reduceIte]
      rw [Finset.sum_range_one, e16, loadHolds_unique l15 (hsum 0 (by decide))]
      simp [fV, H]
    | succ q ih =>
      intro hq
      obtain ⟨lh, -, ea⟩ := holds_tbBlock (htb q (by omega))
      rw [loadHolds_unique lh (hsum (q + 1) hq)] at ea
      simp only [Nat.add_one_ne_zero, ↓reduceIte]
      rw [ea, Finset.sum_range_succ, ← ih (by omega)]
      congr 2
      simp only [tbPrev]
      rcases q with _ | q
      · simp
      · simp only [show q + 1 + 1 ≠ 1 by omega, ↓reduceIte, show q + 1 ≠ 0 by omega,
          Nat.add_sub_cancel]
  -- the answer
  let sFn : Fin 64 → E := fun i ↦ sF i
  let fFn : Fin 8 → E := fun p ↦ fV p
  let gFn : Fin 8 → E := fun b ↦ G.getD b 0
  have hGofFn : List.ofFn gFn = G := by
    apply List.ext_getElem (by rw [List.length_ofFn, hG, hgl])
    intro b h1 h2
    rw [List.getElem_ofFn]
    simp only [gFn]
    rw [List.getD_eq_getElem _ _ h2]
  have himg : ∀ p : Fin 8, H p = wHorner (ofK (ringWK.getD p 0))
      (List.ofFn fun i : Fin 64 ↦ Verifier.ringPsi (sFn i) (List.ofFn gFn)) := by
    intro p
    simp only [H, wHorner, hstep_foldl_eq, hGofFn]
    congr 1
  refine ⟨List.ofFn sFn, List.ofFn fFn ++ List.ofFn gFn, by simp [kBits],
    by simp [ringMapWidth], ?_, ?_, ?_⟩
  · intro t ht
    simp only [List.length_ofFn] at ht
    simp only [List.getElem_ofFn, sFn, sF]
    have h8 : t / 8 < 8 := by omega
    have hrd := hvs (t / 8) h8 (t % 8) (by rw [hvl]; omega)
    rw [← pow_mul, loadHolds_mul_gen_pow, show t / 8 * 8 + t % 8 = t by omega] at hrd
    simp only [h8, ↓reduceDIte]
    rw [List.getD_eq_getElem _ _ (by rw [hvl]; omega)]
    exact hrd
  · intro k hk
    simp only [List.length_append, List.length_ofFn] at hk
    by_cases hk8 : k < 8
    · rw [List.getElem_append_left (by simpa using hk8), List.getElem_ofFn]
      exact hf k hk8
    · rw [List.getElem_append_right (by simpa using hk8)]
      simp only [List.length_ofFn, List.getElem_ofFn, gFn]
      have := hg 0 (by decide) (k - 8) (by omega)
      rw [show 8 + (k - 8) = k by omega] at this
      exact this
  · rw [← hret]
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    have hl : (List.ofFn fFn).length = ringMapWidth := by simp [ringMapWidth]
    rw [List.take_left' hl, List.drop_left' hl, ← guest_target_eq, e270, e269,
      show (9223372036854775808 : ℕ) = 2 ^ 63 from rfl, word_two_pow (by decide), gen_eq_genE]
    congr 1
    have := hrun 7 (by decide)
    simp only [show (7 : ℕ) ≠ 0 by decide, ↓reduceIte, show tbBase 7 + 8 * 7 + 3 = 268 from rfl]
      at this
    rw [this, Finset.sum_range, ← Finset.sum_congr rfl fun p _ ↦ by rw [himg p]]

end
end LeanVM.Guest.B1.VerifySub
