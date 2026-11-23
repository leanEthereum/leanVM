/-
  LeanVM.Guest.B1.Gkr.GlCLayerK

  The kernel facts of the eight layer bodies the forward evaluation needs: they evaluate, their
  reads are not stores, and their tail's equations carry over to the canonical numbering.
-/

module

public import LeanVM.Guest.B1.Gkr.GlCMid
public import LeanVM.Guest.B1.Gkr.GlCTail

/-!
# The layer bodies' kernel facts

* `glc_layer_check`: each of the eight bodies `glcL p o` evaluates (`chk`), and none of its
  reads (`glcFresh p o`: the prefix's, the rounds', the last record's and the children's) is a
  store;
* `good_rho`: an atom of the canonical tail on its renamed equation is on its own equation at
  `σ ∘ glRho p o`, a read given it is not a store.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1 LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The layer function's body. -/
def glcL (p o : ℕ) : List Stmt := glBody p o (glLoopName p o)

/-- A run of `n` rounds' reads from `B`: the four words at `cur` and the eq factor at `pt`. -/
def glcRoundKeys (B cur pt n : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range n).flatMap fun q ↦ [(B + 39 * q, cur, 4 * q), (B + 39 * q + 3, cur, 4 * q + 1),
    (B + 39 * q + 6, cur, 4 * q + 2), (B + 39 * q + 9, cur, 4 * q + 3), (B + 39 * q + 25, pt, q)]

/-- The children's reads, renamed. -/
def glcKidKeys (p o : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range 12).map fun i ↦ (chB 156 i + glD p - 38 * o, 76 + glD p, 4 * (2 - o) + i)

/-- Every read of the body. -/
def glcFresh (p o : ℕ) : List (ℕ × ℕ × ℕ) :=
  glPreKeys ++ glcRoundKeys 58 21 52 (2 * p) ++ glTailKeys p ++
    glcRoundKeys (78 + glD p) (76 + glD p) (67 + glD p) (2 - o) ++ glcKidKeys p o

theorem glc_layer_check : ∀ p < 4, ∀ o < 2, (chk 9 (glcL p o)).isSome = true ∧
    (glcFresh p o).all (fun k ↦ !((storesOf 9 (glcL p o)).map loadKey).contains (some k)) = true := by
  decide +kernel

theorem glc_fresh {p o : ℕ} (hp : p < 4) (ho : o < 2) :
    ∀ k ∈ glcFresh p o, some k ∉ (storesOf 9 (glcL p o)).map loadKey := by
  intro k hk
  have := List.all_eq_true.mp (glc_layer_check p hp o ho).2 k hk
  simpa using this

/-- The canonical tail's atoms: equations whose products are of older values, from `159` on. -/
def tailOkA : Atom → Bool
  | .const .. | .add .. | .copy .. | .keccak .. | .assertEq .. => true
  | .load d q _ => decide (d = .n d.idx) && decide (q = .n q.idx)
  | .mul d x y => decide (156 ≤ d.idx) && decide (x.idx < d.idx) && decide (y.idx < d.idx)
  | _ => false

def tailOkS : Stmt → Bool
  | .atom a => tailOkA a
  | .ret _ => true
  | _ => false

theorem glTail_ok : ∀ o < 2, (glTail o).all tailOkS = true := by decide +kernel

theorem glRho_idx (p o : ℕ) (v : V) : (glRho p o v).idx =
    if v.idx < 58 then v.idx else if v.idx < 117 then v.idx + glD p
    else if v.idx < 156 then v.idx + glD p - 39 * o else v.idx + glD p - 38 * o := by
  unfold glRho; split_ifs <;> rfl

theorem glRho_lt {p o : ℕ} (ho : o < 2) {x d : V} (hd : 156 ≤ d.idx) (hx : x.idx < d.idx) :
    (glRho p o x).idx < (glRho p o d).idx := by
  rw [glRho_idx, glRho_idx]; split_ifs <;> omega

/-- **The canonical tail's equations** at `σ ∘ glRho p o`. -/
theorem good_rho {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {p o : ℕ} (ho : o < 2)
    {a : Atom} (hok : tailOkA a = true) (hg : Good rd S w σ (a.rename (glRho p o)))
    (hld : ∀ d q off, a = .load d q off →
      some ((glRho p o d).idx, (glRho p o q).idx, off) ∉ S.map loadKey) :
    Good rd [] w (σ ∘ glRho p o) a := by
  cases a with
  | const d e => exact hg
  | add d x y => exact hg
  | copy d s => exact hg
  | assertEq x y => trivial
  | keccak ins outs i o' =>
    obtain ⟨h1, h2, h3⟩ := hg
    refine ⟨by simpa using h1, by simpa using h2, fun c hc ↦ ?_⟩
    have := h3 c (by simpa using hc)
    simpa [List.map_map] using this
  | load d q off =>
    simp only [tailOkA, Bool.and_eq_true, decide_eq_true_eq] at hok
    have hn : ∀ v : V, v = .n v.idx → glRho p o v = .n (glRho p o v).idx := fun v hv ↦ by
      rw [hv]; unfold glRho; split_ifs <;> rfl
    have hd := hn d hok.1
    have hq := hn q hok.2
    simp only [Atom.rename, Good] at hg
    rw [hd, hq] at hg
    have := hg.resolve_left (not_mem_of_loadKey (hld d q off rfl))
    refine .inr ?_
    simp only [Function.comp_apply]
    rw [hd, hq]
    exact this
  | mul d x y =>
    simp only [tailOkA, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨h159, hx⟩, hy⟩ := hok
    have hx' := glRho_lt (p := p) ho h159 hx
    have hy' := glRho_lt (p := p) ho h159 hy
    simp only [Atom.rename, Good, hx', hy', and_self, ↓reduceIte] at hg
    simp only [Good, hx, hy, and_self, ↓reduceIte, Function.comp_apply]
    exact hg
  | _ => simp [tailOkA] at hok

theorem mem_renameList_of {r : V → V} : ∀ {ss : List Stmt} {s : Stmt}, s ∈ ss →
    s.rename r ∈ Stmt.renameList r ss
  | [], _, h => absurd h (by simp)
  | t :: ss, s, h => by
    simp only [Stmt.renameList, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · exact .inl rfl
    · exact .inr (mem_renameList_of h)

end
end LeanVM.Guest.B1.Tables
