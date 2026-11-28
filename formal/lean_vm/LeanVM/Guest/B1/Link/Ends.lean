/-
  LeanVM.Guest.B1.Link.Ends

  B1 for `state_ends` (pointer widths `19` to `24`): the state identity's ends.
-/

module

public import LeanVM.Guest.B1.Link.Forms
public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Guest.B1.Common.Find
import LeanVM.Guest.CoreRef

/-!
# `state_ends`

`state_ends(zeta, cbits, w)` (G) multiplies, over `k < w`, `1 + zeta[k]` into `e0` and
`1 + cbits[k] + zeta[k]` into `ec`, and returns both. Its specialization `state_ends__L{w}` is
`seBody w`: block `k` from value `9 k` (`seBlk`), the first without the products. With the cycle
count's bits at `cbits`, `Forms.lean` makes the two `linkEqAt ζ 0` and `linkEqAt ζ cycles`.
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Protocol.Verifier

@[expose] public section

/-- **`state_ends(zeta, cbits, w)`**: the `w` words `zs` at `zeta` and `cs` at `cbits`; it
returns `Π (1 + z_k)` and `Π (1 + c_k + z_k)`. -/
def MeaningStateEnds (w : ℕ) (rd : Reader) : List E → List E → Prop
  | [zeta, cbits], rets => ∃ zs cs : List E, zs.length = w ∧ cs.length = w ∧ ReadsAt rd zeta zs ∧
      ReadsAt rd cbits cs ∧ rets = [prodE (zs.map (1 + ·)), endsProd cs zs]
  | _, _ => False

/-- The specializations' names, `state_ends__L{w}`, `19 ≤ w ≤ 24` (`LINK_W_ARMS`). -/
def seNames : List String := ["state_ends__L19", "state_ends__L20", "state_ends__L21", "state_ends__L22", "state_ends__L23", "state_ends__L24"]

/-- `state_ends__L{w}`'s core IR implies its meaning. -/
def state_ends_SoundP (P : Program) : Prop :=
  ∀ w, 19 ≤ w → w ≤ 24 → ∀ (rd : Reader) (args rets : List E),
    P.Rel rd (seNames.getD (w - 19) "") args rets → MeaningStateEnds w rd args rets

/-! ## The template -/

/-- The words loaded at block `k`: `zeta[k]`, `cbits[k]`. -/
def seZ (k : ℕ) : ℕ := if k = 0 then 2 else 9 * k

def seC (k : ℕ) : ℕ := if k = 0 then 6 else 9 * k + 5

/-- The products after block `k`. -/
def seE0 (k : ℕ) : ℕ := if k = 0 then 4 else 9 * k + 3

def seEc (k : ℕ) : ℕ := 9 * k + 8

/-- Block `k`. -/
def seBlk (k : ℕ) : List Stmt :=
  if k = 0 then
    [.atom (.load (.n 2) (.n 0) 0), .atom (.const (.n 3) (word 1 0)), .atom (.add (.n 4) (.n 3) (.n 2)),
      .atom (.const (.n 5) (word 1 0)), .atom (.load (.n 6) (.n 1) 0), .atom (.add (.n 7) (.n 5) (.n 6)),
      .atom (.add (.n 8) (.n 7) (.n 2))]
  else
    [.atom (.load (.n (9 * k)) (.n 0) k), .atom (.const (.n (9 * k + 1)) (word 1 0)),
      .atom (.add (.n (9 * k + 2)) (.n (9 * k + 1)) (.n (9 * k))),
      .atom (.mul (.n (9 * k + 3)) (.n (seE0 (k - 1))) (.n (9 * k + 2))),
      .atom (.const (.n (9 * k + 4)) (word 1 0)), .atom (.load (.n (9 * k + 5)) (.n 1) k),
      .atom (.add (.n (9 * k + 6)) (.n (9 * k + 4)) (.n (9 * k + 5))),
      .atom (.add (.n (9 * k + 7)) (.n (9 * k + 6)) (.n (9 * k))),
      .atom (.mul (.n (9 * k + 8)) (.n (seEc (k - 1))) (.n (9 * k + 7)))]

/-- The expansion of `state_ends__L{w}`, `w ≥ 1`. -/
def seBody (w : ℕ) : List Stmt :=
  ((List.range w).map seBlk).flatten ++
    [.atom (.copy (.n (9 * w)) (.n (seE0 (w - 1)))), .atom (.copy (.n (9 * w + 1)) (.n (seEc (w - 1)))),
      .ret [.n (9 * w), .n (9 * w + 1)]]

/-- What block `k` asks. -/
def SeOk (rd : Reader) (σ : Val) (k : ℕ) : Prop :=
  LoadHolds rd (σ (.n 0)) k (σ (.n (seZ k))) ∧ LoadHolds rd (σ (.n 1)) k (σ (.n (seC k))) ∧
    σ (.n (seE0 k)) = (if k = 0 then 1 else σ (.n (seE0 (k - 1)))) * (1 + σ (.n (seZ k))) ∧
    σ (.n (seEc k)) = (if k = 0 then 1 else σ (.n (seEc (k - 1)))) *
      (1 + σ (.n (seC k)) + σ (.n (seZ k)))

theorem holds_seBlk {C : CallRel} {rd : Reader} {σ : Val} (k : ℕ) (kret : List E → Prop)
    (h : Stmt.HoldsList C rd σ (seBlk k) True kret) : SeOk rd σ k := by
  unfold seBlk at h
  split_ifs at h with hk
  · subst hk
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one] at h
    obtain ⟨l2, h3, h4, h5, l6, h7, h8⟩ := h
    refine ⟨l2, l6, ?_, ?_⟩ <;> simp only [seE0, seEc, seZ, seC, ↓reduceIte, one_mul]
    · rw [h4, h3]
    · rw [show 9 * 0 + 8 = 8 from rfl, h8, h7, h5]
  · have eZ : seZ k = 9 * k := by simp [seZ, hk]
    have eC : seC k = 9 * k + 5 := by simp [seC, hk]
    have e0 : seE0 k = 9 * k + 3 := by simp [seE0, hk]
    have eC' : seEc k = 9 * k + 8 := rfl
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one] at h
    obtain ⟨l0, h1, h2, h3, h4, l5, h6, h7, h8⟩ := h
    refine ⟨by rw [eZ]; exact l0, by rw [eC]; exact l5, ?_, ?_⟩
    · rw [e0, eZ, h3, h2, h1]
      simp only [hk, ↓reduceIte]
    · rw [eC', eC, eZ, h8, h7, h6, h4]
      simp only [hk, ↓reduceIte]

theorem seBlk_noRet (k : ℕ) : Stmt.noRetList (seBlk k) = true := by
  unfold seBlk; split <;> rfl

theorem zipWith_range_map {α β γ : Type} (f : α → β → γ) (g : ℕ → α) (h : ℕ → β) (n : ℕ) :
    List.zipWith f ((List.range n).map g) ((List.range n).map h) =
      (List.range n).map fun i ↦ f (g i) (h i) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ, List.zipWith_append, ih]

/-- **The template's relation implies its meaning.** -/
theorem se_sound (w : ℕ) (hw : 1 ≤ w) {f : Fn}
    (hfind : coreProgram.find? (seNames.getD (w - 19) "") = some f)
    (hparams : f.params = [.n 0, .n 1]) (hbody : f.body = seBody w) (rd : Reader)
    (args rets : List E) :
    coreProgram.Rel rd (seNames.getD (w - 19) "") args rets → MeaningStateEnds w rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams, seBody]
  simp only [holdsList_append, holdsList_range_flatten w seBlk seBlk_noRet,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
  rintro ⟨σ, rfl, hblk, h0, h1, hret⟩
  have hb := fun k (hk : k < w) ↦ holds_seBlk (C := coreProgram.Rel rd) k _ (hblk k hk)
  let z : ℕ → E := fun k ↦ σ (.n (seZ k))
  let c : ℕ → E := fun k ↦ σ (.n (seC k))
  have hv : ∀ k < w, σ (.n (seE0 k)) = prodE ((List.range (k + 1)).map fun i ↦ 1 + z i) ∧
      σ (.n (seEc k)) = prodE ((List.range (k + 1)).map fun i ↦ 1 + c i + z i) := by
    intro k hk
    induction k with
    | zero =>
      obtain ⟨-, -, e0, ec⟩ := hb 0 hk
      simp only [↓reduceIte, one_mul] at e0 ec
      exact ⟨by rw [e0]; simp [prodE, z], by rw [ec]; simp [prodE, z, c]⟩
    | succ k ih =>
      obtain ⟨-, -, e0, ec⟩ := hb (k + 1) hk
      obtain ⟨i0, ic⟩ := ih (by omega)
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at e0 ec
      have hr : List.range (k + 1 + 1) = List.range (k + 1) ++ [k + 1] := List.range_succ
      rw [e0, ec, i0, ic, hr, List.map_append, List.map_append, prodE_append, prodE_append]
      exact ⟨by simp only [List.map_cons, List.map_nil, prodE_cons, prodE_nil, mul_one]; rfl,
        by simp only [List.map_cons, List.map_nil, prodE_cons, prodE_nil, mul_one]; rfl⟩
  obtain ⟨v0, vc⟩ := hv (w - 1) (by omega)
  rw [Nat.sub_add_cancel hw] at v0 vc
  refine ⟨(List.range w).map z, (List.range w).map c, by simp, by simp, fun k hk ↦ ?_,
    fun k hk ↦ ?_, ?_⟩
  · simp only [List.length_map, List.length_range] at hk
    simpa [z] using (hb k hk).1
  · simp only [List.length_map, List.length_range] at hk
    simpa [c] using (hb k hk).2.1
  · rw [← hret, h0, h1, v0, vc, endsProd, zipWith_range_map, List.map_map]
    rfl

/-! ## The specializations -/

set_option maxRecDepth 100000 in
theorem state_ends_L19_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (seNames.getD 0 "") args rets → MeaningStateEnds 19 rd args rets :=
  se_sound 19 (by omega) (f := fn% «state_ends__L19»)
    (coreProgram_find?_at (j := idx% «state_ends__L19») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem state_ends_L20_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (seNames.getD 1 "") args rets → MeaningStateEnds 20 rd args rets :=
  se_sound 20 (by omega) (f := fn% «state_ends__L20»)
    (coreProgram_find?_at (j := idx% «state_ends__L20») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem state_ends_L21_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (seNames.getD 2 "") args rets → MeaningStateEnds 21 rd args rets :=
  se_sound 21 (by omega) (f := fn% «state_ends__L21»)
    (coreProgram_find?_at (j := idx% «state_ends__L21») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem state_ends_L22_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (seNames.getD 3 "") args rets → MeaningStateEnds 22 rd args rets :=
  se_sound 22 (by omega) (f := fn% «state_ends__L22»)
    (coreProgram_find?_at (j := idx% «state_ends__L22») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem state_ends_L23_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (seNames.getD 4 "") args rets → MeaningStateEnds 23 rd args rets :=
  se_sound 23 (by omega) (f := fn% «state_ends__L23»)
    (coreProgram_find?_at (j := idx% «state_ends__L23») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem state_ends_L24_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (seNames.getD 5 "") args rets → MeaningStateEnds 24 rd args rets :=
  se_sound 24 (by omega) (f := fn% «state_ends__L24»)
    (coreProgram_find?_at (j := idx% «state_ends__L24») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

/-- **`state_ends`' core IR implies its meaning**, every specialization. -/
theorem state_ends_sound : state_ends_SoundP coreProgram := by
  intro w h1 h2
  interval_cases w
  exacts [state_ends_L19_sound, state_ends_L20_sound, state_ends_L21_sound, state_ends_L22_sound, state_ends_L23_sound, state_ends_L24_sound]

end
end LeanVM.Guest.B1.Link
