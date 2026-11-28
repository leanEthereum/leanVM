/-
  LeanVM.Guest.B1.VsC.CopyLoopA

  `verify_keccak`'s copy loops complete placed, with no words of their own.
-/

module

public import LeanVM.Guest.B1.VsC.LoopFlat
public import LeanVM.Guest.B1.VsC.LrC
public import LeanVM.Guest.B1.KeccakGkr.CopyLoop
public import LeanVM.Guest.Complete.TransferA

/-!
# `verify_keccak_loop{0,1,2}`, placed

A copy loop (the guest stream's `copyLoopT`) at iteration `j` (`x = g^j`, bound `g^m`) loads
`src·x`'s word and stores it at `dst·x`. On a memory holding the same `m` words `l` at `src` and at
`dst` (`ClMem`), its forward evaluation holds every atom: the load reads `l[j]`, which the store
finds at `dst·g^j`.

* `cl_loop`: the loop completes from iteration `j < m`, with no words of its own.
* `cl_shape`: every valid tree of it from iteration `j` has block `lpB fs name m j`, ends at its
  cursor and loads from the region holding both arrays.
* `cl_placed`: placed by the transfer `callAtA_of_callCompletes0`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.Value LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template, numbered -/

/-- The copy loop's atoms before its tail call. -/
def clA : List Atom :=
  [.mul (.n 4) (.n 3) (.n 0), .load (.n 5) (.n 4) 0, .mul (.n 6) (.n 2) (.n 0), .load (.n 5) (.n 6) 0,
    .const (.n 7) (word 2 0), .mul (.n 8) (.n 0) (.n 7), .add (.n 9) (.n 8) (.n 1),
    .const (.n 10) (word 2 0), .mul (.n 11) (.n 0) (.n 10)]

/-- The copy loop's tail call's arguments. -/
def clT : List V := [.n 11, .n 1, .n 2, .n 3]

/-- The copy loop named `name`. -/
def clBody (name : String) : List Stmt := (clA.map Stmt.atom ++ [Stmt.callIf (.n 9) name clT]) ++ [.ret []]

theorem copyLoopT_eq (name : String) : copyLoopT name = clBody name := rfl

/-- The three copy loops. -/
def vkLoopNames : List String := ["__loop0_verify_keccak", "__loop1_verify_keccak", "__loop2_verify_keccak"]

/-- The store. -/
def clStore : Atom := .load (.n 5) (.n 6) 0

/-- The pointers the loads go through: `src·x` and `dst·x`, one word each. -/
def clPs : List (ℕ × ℕ) := [(4, 1), (6, 1)]

theorem cl_chk (name : String) : chk 4 (clBody name) = some 12 := rfl

theorem cl_stores (name : String) : storesOf 4 (clBody name) = [clStore] := rfl

theorem cl_ok : clA.all (loadOkB clPs) = true := by decide

set_option maxRecDepth 100000 in
theorem cl_find {name : String} (h : name ∈ vkLoopNames) :
    ∃ fn, coreProgram.find? name = some fn ∧ fn.body = clBody name ∧ fn.params = (List.range 4).map V.n := by
  simp only [vkLoopNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · exact ⟨_, find_copyLoop11, copyLoop_body11, rfl⟩
  · exact ⟨_, find_copyLoop12, copyLoop_body12, rfl⟩
  · exact ⟨_, find_copyLoop13, copyLoop_body13, rfl⟩

/-! ## An iteration -/

/-- The loop's arguments at iteration `j`, bound `g^m`, `dst` at `id`, `src` at `is`. -/
def clArgs (j m id is : ℕ) : List E := [gen ^ j, gen ^ m, ptrAt id, ptrAt is]

/-- What the loop reads: the same words at `src` and `dst`. -/
def ClMem (id is : ℕ) (l : List E) (rd : Reader) : Prop := ReadsAt rd (ptrAt is) l ∧ ReadsAt rd (ptrAt id) l

theorem cl_vals {rd : Reader} {σ : Val} {j m id is : ℕ} (hp : ∀ i < 4, σ (.n i) = (clArgs j m id is).getD i 0)
    (hA : ∀ a ∈ clA, needsSide a = false → a.Holds rd σ) :
    σ (.n 4) = ptrAt (is + j) ∧ σ (.n 6) = ptrAt (id + j) ∧ σ (.n 9) = gen ^ (j + 1) + gen ^ m ∧
      clT.map σ = clArgs (j + 1) m id is := by
  have e4 : σ (.n 4) = σ (.n 3) * σ (.n 0) := hA (.mul (.n 4) (.n 3) (.n 0)) (by simp [clA]) (by decide)
  have e6 : σ (.n 6) = σ (.n 2) * σ (.n 0) := hA (.mul (.n 6) (.n 2) (.n 0)) (by simp [clA]) (by decide)
  have e7 : σ (.n 7) = word 2 0 := hA (.const (.n 7) (word 2 0)) (by simp [clA]) rfl
  have e8 : σ (.n 8) = σ (.n 0) * σ (.n 7) := hA (.mul (.n 8) (.n 0) (.n 7)) (by simp [clA]) (by decide)
  have e9 : σ (.n 9) = σ (.n 8) + σ (.n 1) := hA (.add (.n 9) (.n 8) (.n 1)) (by simp [clA]) rfl
  have e10 : σ (.n 10) = word 2 0 := hA (.const (.n 10) (word 2 0)) (by simp [clA]) rfl
  have e11 : σ (.n 11) = σ (.n 0) * σ (.n 10) := hA (.mul (.n 11) (.n 0) (.n 10)) (by simp [clA]) (by decide)
  have p0 : σ (.n 0) = gen ^ j := hp 0 (by decide)
  have p1 : σ (.n 1) = gen ^ m := hp 1 (by decide)
  have p2 : σ (.n 2) = ptrAt id := hp 2 (by decide)
  have p3 : σ (.n 3) = ptrAt is := hp 3 (by decide)
  refine ⟨by rw [e4, p3, p0, ptrAt_mul_gen], by rw [e6, p2, p0, ptrAt_mul_gen], ?_, ?_⟩
  · rw [e9, e8, e7, p0, p1, word_gen, pow_succ]
  · simp only [clT, List.map_cons, List.map_nil, clArgs]
    rw [e11, e10, p0, word_gen, ← pow_succ, p1, p2, p3]

variable {kd : ℕ}

/-- **Iteration `j` of a copy loop completes**, from the next one's. -/
theorem cl_step {name : String} (hn : name ∈ vkLoopNames) {id is m : ℕ} {l : List E} (hl : l.length = m)
    {j : ℕ} (hj : j < m)
    (hnext : j + 1 < m → CallCompletes0 kd name (clArgs (j + 1) m id is) [] (ClMem id is l) PostQuiet) :
    CallCompletes0 kd name (clArgs j m id is) [] (ClMem id is l) PostQuiet := by
  obtain ⟨fn, hfind, hbody, hpar⟩ := cl_find hn
  set args := clArgs j m id is with hargs
  have hchk : chk args.length fn.body = some 12 := by rw [hbody]; exact cl_chk name
  refine callCompletes0_loopFlat hfind hbody (by rw [hpar]; rfl) cl_ok
    (fun rd => fwdVal rd (fun _ => 0) args fn.body) fun rd hlow hP => ?_
  set σ := fwdVal rd (fun _ => 0) args fn.body with hσ
  obtain ⟨hsrc, hdst⟩ := hP
  have hmem : ∀ a ∈ clA, Stmt.atom a ∈ fn.body := fun a ha => by
    rw [hbody]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨a, ha, rfl⟩))
  have hNS : ∀ a ∈ clA, needsSide a = false → a.Holds rd σ := fun a ha hn => fwd_holds_noSide hchk (hmem a ha) hn
  have hp : ∀ i < 4, σ (.n i) = args.getD i 0 := fun i hi => fwd_param hchk (by simpa [hargs, clArgs] using hi)
  obtain ⟨v4, v6, vg, vt⟩ := cl_vals hp hNS
  have hS : storesOf args.length fn.body = [clStore] := by rw [hbody]; exact cl_stores name
  -- the load reads `l[j]`
  have hld : (Atom.load (.n 5) (.n 4) 0).Holds rd σ := by
    refine fwd_holds_load hchk (hmem _ (by simp [clA])) (by rw [hS]; simp [clStore]) ?_
    rw [← hσ, v4]; exact ⟨_, readsAt_off hsrc (by omega)⟩
  have h5 : σ (.n 5) = l[j]'(by omega) := by
    have h := hld
    simp only [Atom.Holds, v4] at h
    exact loadHolds_unique h (readsAt_off hsrc (m := j) (o := 0) (by omega))
  refine ⟨by rw [hpar]; exact fwd_params hchk, fun a ha => ?_, ?_, fun hz => ?_⟩
  · by_cases hst : a = clStore
    · subst hst
      show LoadHolds rd (σ (.n 6)) 0 (σ (.n 5))
      rw [v6, h5]; exact readsAt_off hdst (by omega)
    · by_cases hl5 : a = .load (.n 5) (.n 4) 0
      · subst hl5; exact hld
      · refine hNS a ha ?_
        simp only [clA, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact absurd rfl hl5 | exact absurd rfl hst
  · rw [vg]; exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _)
  · have hne : j + 1 ≠ m := fun h => hz (by rw [vg, h]; exact CharTwo.add_self_eq_zero _)
    obtain ⟨t, htn, hv2, hb2, hq2⟩ := hnext (by omega) rd hlow ⟨hsrc, hdst⟩
    exact ⟨t, htn, by rw [vt]; exact hv2, hb2, hq2⟩

/-- **A copy loop completes from iteration `j`**, every `j < m`. -/
theorem cl_loop {name : String} (hn : name ∈ vkLoopNames) {id is m : ℕ} {l : List E} (hl : l.length = m) :
    ∀ r j, m = j + r + 1 →
      CallCompletes0 kd name (clArgs j m id is) [] (ClMem id is l) PostQuiet := by
  intro r
  induction r with
  | zero => intro j hj; exact cl_step hn hl (by omega) (fun h => absurd h (by omega))
  | succ r IH => intro j hj; exact cl_step hn hl (by omega) (fun _ => IH (j + 1) (by omega))

/-! ## Shapes -/

/-- What a copy loop of `m` words loads from: both arrays. -/
def ClRegion (id is m : ℕ) (R : ℕ → Prop) : Prop := (∀ i < m, R (is + i)) ∧ ∀ i < m, R (id + i)

theorem cl_loopB {name : String} (hn : name ∈ vkLoopNames) : coreProgram.loop name = true := by
  simp only [vkLoopNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl
  · rw [Program.loop_of_find? find_copyLoop11, Fn.loop, copyLoop_body11]
    simp [copyLoopT]; rfl
  · rw [Program.loop_of_find? find_copyLoop12, Fn.loop, copyLoop_body12]
    simp [copyLoopT]; rfl
  · rw [Program.loop_of_find? find_copyLoop13, Fn.loop, copyLoop_body13]
    simp [copyLoopT]; rfl

/-- **Every valid tree of a copy loop from iteration `j < m` has its shape.** -/
theorem cl_shape {fs : String → ℕ} {al : String → Bool} {name : String} (hn : name ∈ vkLoopNames) {id is m : ℕ}
    (hm : m < 2 ^ 64 - 1) {R : ℕ → Prop} (hR : ClRegion id is m R) :
    ∀ r j, m = j + r + 1 → ∀ rd t, t.name = name →
      t.Valid coreProgram rd (clArgs j m id is) [] → t.BufsOk coreProgram →
      ShapeR fs al (lpB fs name m j) _root_.id R t := by
  obtain ⟨fn, hfind, hbody, hpar⟩ := cl_find hn
  have hbase : ∀ j, j < m → ∀ rd σ, fn.params.map σ = clArgs j m id is → (∀ a ∈ clA, a.Holds rd σ) →
      (∀ q ∈ clPs, ∃ b, σ (.n q.1) = ptrAt b ∧ ∀ o < q.2, R (b + o)) ∧
        σ (.n 9) = gen ^ (j + 1) + gen ^ m ∧ clT.map σ = clArgs (j + 1) m id is := by
    intro j hj rd σ hp hA
    have hp' : ∀ i < 4, σ (.n i) = (clArgs j m id is).getD i 0 := fun i hi => by
      rw [← hp, hpar]; simp [List.getD_eq_getElem?_getD, hi]
    obtain ⟨v4, v6, vg, vt⟩ := cl_vals hp' fun a ha _ => hA a ha
    refine ⟨fun q hq => ?_, vg, vt⟩
    simp only [clPs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨is + j, v4, fun o ho => by rw [Nat.add_assoc]; exact hR.1 _ (by simp only at ho; omega)⟩
    · exact ⟨id + j, v6, fun o ho => by rw [Nat.add_assoc]; exact hR.2 _ (by simp only at ho; omega)⟩
  have e : ∀ j, j < m → fs name + lpB fs name m (j + 1) = lpB fs name m j := fun j hj => by
    simp only [lpB]; rw [show m - j = (m - (j + 1)) + 1 by omega]; ring
  intro r
  induction r with
  | zero =>
    intro j hj rd t htn hv hbt
    have h := shapeR_loopFlat (fs := fs) (al := al) (args := clArgs j m id is) (R := R)
      (Bt := lpB fs name m (j + 1)) hfind hbody (cl_loopB hn) cl_ok ?_ rd t htn hv hbt
    · rwa [e j (by omega)] at h
    · intro rd' σ hp hA
      obtain ⟨hb, vg, -⟩ := hbase j (by omega) rd' σ hp hA
      refine ⟨hb, fun _ => by simp only [lpB]; rw [show m - (j + 1) = 0 by omega]; ring, fun hz => ?_⟩
      exact absurd (by rw [vg, show j + 1 = m by omega]; exact CharTwo.add_self_eq_zero _) hz
  | succ r IH =>
    intro j hj rd t htn hv hbt
    have h := shapeR_loopFlat (fs := fs) (al := al) (args := clArgs j m id is) (R := R)
      (Bt := lpB fs name m (j + 1)) hfind hbody (cl_loopB hn) cl_ok ?_ rd t htn hv hbt
    · rwa [e j (by omega)] at h
    · intro rd' σ hp hA
      obtain ⟨hb, vg, vt⟩ := hbase j (by omega) rd' σ hp hA
      refine ⟨hb, fun hz => absurd hz ?_, fun _ t' hn' hv' hb'' => ?_⟩
      · rw [vg]; exact (gen_add_ne' (by omega) (by omega)).not.mpr (by omega)
      · rw [vt] at hv'
        exact IH (j + 1) (by omega) rd' t' hn' hv' hb''

theorem cl_pure {name : String} (hn : name ∈ vkLoopNames) : coreProgram.PureIn [name] := by
  intro g hg fn' hf'
  rw [List.mem_singleton] at hg
  subst hg
  simp only [vkLoopNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl
  · rw [find_copyLoop11, Option.some.injEq] at hf'; subst hf'; rw [copyLoop_body11]; decide +kernel
  · rw [find_copyLoop12, Option.some.injEq] at hf'; subst hf'; rw [copyLoop_body12]; decide +kernel
  · rw [find_copyLoop13, Option.some.injEq] at hf'; subst hf'; rw [copyLoop_body13]; decide +kernel

/-- **A copy loop completes placed** from its first iteration, `0 < m`, with no words of its own,
ending at its cursor. -/
theorem cl_placed {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {name : String}
    (hn : name ∈ vkLoopNames) {id is m : ℕ} {l : List E} (hl : l.length = m) (h0 : 0 < m) (hm : m < 2 ^ 64 - 1)
    {R : ℕ → Prop} (hR : ClRegion id is m R) (fp c : ℕ) :
    CallAtA fs al cert k name (clArgs 0 m id is) [] R (fun _ => False) (fun _ => True) (ClMem id is l)
      PostQuiet (lpB fs name m 0) fp c c :=
  callAtA_of_callCompletes0 (cl_pure hn) (List.mem_singleton_self _) le_rfl
    (cl_loop hn hl (m - 1) 0 (by omega))
    fun rd t _ _ htn hv hb _ =>
      let h := cl_shape (fs := fs) (al := al) hn hm hR (m - 1) 0 (by omega) rd t htn hv hb
      ⟨h.1, h.2.1 c, h.2.2.1, h.2.2.2⟩

end
end LeanVM.Guest.B1.VsC
