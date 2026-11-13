/-
  LeanVM.Guest.B1.Sig.CompleteBasic

  Completeness of single atoms and of blocks of atoms: a valuation updated at fresh values makes
  the block hold.
-/

module

public import LeanVM.Guest.B1.Sig.Frame
public import LeanVM.Guest.B1.Sig.KeccakMsg

/-!
# Complete atoms

`Completes` (`Frame`) of the atoms the templates are made of, each defining fresh values from
values numbered below: a constant, a sum, a product, a copy, a load, a hint and a `KECCAK` (its
outputs `kOut`, the cells of Keccak-f[1600] of its canonical inputs). `completes_atoms`: a block of
atoms holds before any true continuation when its atoms do.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash

@[expose] public section

variable {C : CallRel} {rd : Reader}

theorem holdsList_of_atomsHold : ∀ {ss : List Stmt}, atomsOnly ss = true → ∀ {σ : Val},
    AtomsHold rd σ ss → ∀ (next : Prop) (kret : List E → Prop), next →
      Stmt.HoldsList C rd σ ss next kret
  | [], _, _, _, _, _, hn => hn
  | .atom a :: ss, hs, σ, h, next, kret, hn => by
      simp only [atomsOnly] at hs
      exact ⟨h a (List.mem_cons_self ..), holdsList_of_atomsHold hs
        (fun b hb => h b (List.mem_cons_of_mem _ hb)) next kret hn⟩
  | .ite .. :: _, hs, _, _, _, _, _ | .match_ .. :: _, hs, _, _, _, _, _
  | .call .. :: _, hs, _, _, _, _, _ | .callIf .. :: _, hs, _, _, _, _, _
  | .dispatch .. :: _, hs, _, _, _, _, _ | .ret _ :: _, hs, _, _, _, _, _ => by
      simp [atomsOnly] at hs

/-- **A block of atoms completes** when its atoms hold of an extension. -/
theorem completes_atoms {lo hi : Nat} {ss : List Stmt} (hs : atomsOnly ss = true) {σ σ' : Val}
    {Post : Val → Prop} (he : Ext lo hi σ σ') (hp : Post σ') (h : AtomsHold rd σ' ss) :
    Completes C rd lo hi ss σ Post :=
  ⟨σ', he, hp, fun next kret hn => holdsList_of_atomsHold hs h next kret hn⟩

theorem upds_single_ne (σ : Val) {k : Nat} (e : E) {v : V} (hv : v ≠ .n k) :
    upds σ [(k, e)] v = σ v := by
  simp only [upds]
  exact Function.update_of_ne hv _ _

theorem ne_of_nb {v : V} {lo : Nat} (h : ∃ j < lo, v = .n j) {k : Nat} (hk : lo ≤ k) : v ≠ .n k := by
  obtain ⟨j, hj, rfl⟩ := h
  intro e
  simp only [V.mk.injEq] at e
  omega

/-! ## One atom -/

theorem cst_complete (σ : Val) (b : Nat) (c : E) :
    Completes C rd b (b + 1) [cst b c] σ (fun σ' => σ' (.n b) = c) :=
  completes_atoms rfl (upds_ext σ [(b, c)] (by simp)) (upds_cons_self σ b c [])
    (fun a ha => by
      simp only [cst, List.mem_singleton, Stmt.atom.injEq] at ha
      subst ha
      exact upds_cons_self σ b c [])

theorem addS_complete (σ : Val) (d : Nat) {x y : V} (hx : ∃ j < d, x = .n j) (hy : ∃ j < d, y = .n j) :
    Completes C rd d (d + 1) [addS (.n d) x y] σ (fun σ' => σ' (.n d) = σ x + σ y) := by
  refine completes_atoms rfl (upds_ext σ [(d, σ x + σ y)] (by simp)) (upds_cons_self σ d _ [])
    (fun a ha => ?_)
  simp only [addS, List.mem_singleton, Stmt.atom.injEq] at ha
  subst ha
  show upds σ [(d, σ x + σ y)] (.n d) = upds σ [(d, σ x + σ y)] x + upds σ [(d, σ x + σ y)] y
  rw [upds_cons_self, upds_single_ne σ _ (ne_of_nb hx le_rfl), upds_single_ne σ _ (ne_of_nb hy le_rfl)]

theorem mulS_complete (σ : Val) (d : Nat) {x y : V} (hx : ∃ j < d, x = .n j) (hy : ∃ j < d, y = .n j) :
    Completes C rd d (d + 1) [mulS (.n d) x y] σ (fun σ' => σ' (.n d) = σ x * σ y) := by
  refine completes_atoms rfl (upds_ext σ [(d, σ x * σ y)] (by simp)) (upds_cons_self σ d _ [])
    (fun a ha => ?_)
  simp only [mulS, List.mem_singleton, Stmt.atom.injEq] at ha
  subst ha
  show upds σ [(d, σ x * σ y)] (.n d) = upds σ [(d, σ x * σ y)] x * upds σ [(d, σ x * σ y)] y
  rw [upds_cons_self, upds_single_ne σ _ (ne_of_nb hx le_rfl), upds_single_ne σ _ (ne_of_nb hy le_rfl)]

theorem copyS_complete (σ : Val) (d : Nat) {x : V} (hx : ∃ j < d, x = .n j) :
    Completes C rd d (d + 1) [copyS (.n d) x] σ (fun σ' => σ' (.n d) = σ x) := by
  refine completes_atoms rfl (upds_ext σ [(d, σ x)] (by simp)) (upds_cons_self σ d _ [])
    (fun a ha => ?_)
  simp only [copyS, List.mem_singleton, Stmt.atom.injEq] at ha
  subst ha
  show upds σ [(d, σ x)] (.n d) = upds σ [(d, σ x)] x
  rw [upds_cons_self, upds_single_ne σ _ (ne_of_nb hx le_rfl)]

theorem loadS_complete (σ : Val) (d : Nat) {p : V} (hp : ∃ j < d, p = .n j) {off : Nat} {w : E}
    (hl : LoadHolds rd (σ p) off w) :
    Completes C rd d (d + 1) [loadS (.n d) p off] σ (fun σ' => σ' (.n d) = w) := by
  refine completes_atoms rfl (upds_ext σ [(d, w)] (by simp)) (upds_cons_self σ d _ [])
    (fun a ha => ?_)
  simp only [loadS, List.mem_singleton, Stmt.atom.injEq] at ha
  subst ha
  show LoadHolds rd (upds σ [(d, w)] p) off (upds σ [(d, w)] (.n d))
  rw [upds_cons_self, upds_single_ne σ _ (ne_of_nb hp le_rfl)]
  exact hl

/-- `n` values from `b` updated to `f`. -/
def updRun (σ : Val) (b n : Nat) (f : Nat → E) : Val :=
  upds σ ((List.range n).map fun j => (b + j, f j))

theorem updRun_at (σ : Val) (b n : Nat) (f : Nat → E) {j : Nat} (hj : j < n) :
    updRun σ b n f (.n (b + j)) = f j := by
  unfold updRun
  generalize hl : (List.range n).map (fun j => (b + j, f j)) = l
  have hm : (b + j, f j) ∈ l := by rw [← hl]; simp; omega
  have hu : ∀ p ∈ l, ∀ q ∈ l, p.1 = q.1 → p = q := by
    rw [← hl]
    simp only [List.mem_map, List.mem_range]
    rintro _ ⟨i, -, rfl⟩ _ ⟨i', -, rfl⟩ e
    simp only at e
    have : i = i' := by omega
    subst this
    rfl
  clear hl
  induction l with
  | nil => simp at hm
  | cons p l ih =>
      obtain ⟨k, e⟩ := p
      by_cases hk : k = b + j
      · subst hk
        have : e = f j := by
          rcases List.mem_cons.mp hm with h | h
          · cases h; rfl
          · have := hu _ (List.mem_cons_self ..) _ (List.mem_cons_of_mem _ h) rfl
            cases this; rfl
        subst this
        exact upds_cons_self _ _ _ _
      · rw [upds_cons_ne σ e l (Ne.symm hk)]
        exact ih (by
          rcases List.mem_cons.mp hm with h | h
          · cases h; exact absurd rfl hk
          · exact h) fun p hp q hq => hu p (List.mem_cons_of_mem _ hp) q (List.mem_cons_of_mem _ hq)

theorem updRun_ext (σ : Val) (b n : Nat) (f : Nat → E) : Ext b (b + n) σ (updRun σ b n f) :=
  upds_ext σ _ (by simp only [List.mem_map, List.mem_range]; rintro _ ⟨j, hj, rfl⟩; simp; omega)

theorem updRun_below (σ : Val) (b n : Nat) (f : Nat → E) {v : V} (hv : ∃ j < b, v = .n j) :
    updRun σ b n f v = σ v := by
  obtain ⟨j, hj, rfl⟩ := hv
  exact (updRun_ext σ b n f).apply (Or.inl hj)

/-- The outputs of a `KECCAK` of the inputs' words. -/
def kOut (ws : List E) (inOdd outOdd : Bool) (c : Nat) : E :=
  if h : c < 13 then cellsOfState (keccakF1600 (stateOfCells (cells13 ws) inOdd)) outOdd ⟨c, h⟩ else 0

/-- **A `KECCAK` completes**: its `n` outputs (one, two or thirteen, its `out_cells`) are `kOut`
of its inputs. -/
theorem kecS_complete (σ : Val) {ins : List V} (o : Nat) {n : Nat}
    (hn : n = 1 ∨ n = 2 ∨ n = 13) (hl : ins.length = 13)
    (hin : ∀ v ∈ ins, ∃ j < o, v = .n j) (inOdd outOdd : Bool) :
    Completes C rd o (o + n) [kecS ins (runV o n) inOdd outOdd] σ
      (fun σ' => ∀ c < n, σ' (.n (o + c)) = kOut (ins.map σ) inOdd outOdd c) := by
  obtain ⟨oc, rfl⟩ := exists_cellCount hn
  have hins : ins.map (updRun σ o oc.cellCount (kOut (ins.map σ) inOdd outOdd)) = ins.map σ :=
    List.map_congr_left fun v hv => updRun_below σ o _ _ (hin v hv)
  refine completes_atoms rfl (updRun_ext σ o _ _) (fun c hc => updRun_at σ o _ _ hc)
    (fun a ha => ?_)
  simp only [kecS, List.mem_singleton, Stmt.atom.injEq] at ha
  subst ha
  refine ⟨hl, oc, by simp [runV], ?_⟩
  rw [hins]
  intro c hco
  simp only [cells13, runV, List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hco, Option.map_some, Option.getD_some, Function.comp]
  rw [updRun_at σ o _ _ hco, kOut]
  simp [c.isLt]

end
end LeanVM.Guest.B1.Sig
