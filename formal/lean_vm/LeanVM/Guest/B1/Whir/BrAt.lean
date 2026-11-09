/-
  LeanVM.Guest.B1.Whir.BrAt

  The levels of the Spec's honest chain, one at a time.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Guest.B1.Whir.BrChain

/-!
# The chain's levels, one at a time

From an honest chain (`SpChain`): each level's facts (`L.Ok`, its index, its Spec level, its
`fin`), each level after the first opens the commitment the previous one read
(`(Ls[i+1]).root = (Ls[i]).dn`), each level starts where the previous ends (`ws`, `F`), and every
level's fold challenges are a prefix of the last level's (`chain_folds`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {logN lane : ℕ}

/-- What the chain gives of a level. -/
structure SpAt (logN : ℕ) (cfg : List Whir.Level) (lvl n i : ℕ) (L : SpLv) : Prop where
  ok : ∃ R d, L.Ok R d
  index : L.index = lvl + i
  logN : L.logN = logN
  level : L.level = cfg.getD i ⟨0, 0, 0⟩
  fin : L.fin = true ↔ i + 1 = n

theorem chain_at : ∀ (cfg : List Whir.Level) (lvl : ℕ) (ws : WhirStateT) (F : Fs) (xs : List E)
    (os : List (List Opening)) (R : List (Digest × ℕ × ℕ)) (Ls : List SpLv) (res : WhirEnd × FSt),
    SpChain logN lane lvl cfg ws F xs os R Ls res →
    Ls.length = cfg.length ∧ (∀ i < Ls.length, SpAt logN cfg lvl Ls.length i (Ls.getD i default)) ∧
      (Ls.getD 0 default).ws = ws ∧ (Ls.getD 0 default).F = F ∧
      (∃ d, (Ls.getD 0 default).Ok R d) ∧
      (∀ i, i + 1 < Ls.length → (Ls.getD (i + 1) default).ws = (Ls.getD i default).wsEnd ∧
        (Ls.getD (i + 1) default).F = (Ls.getD i default).Fend)
  | [level], lvl, ws, F, xs, os, R, [L], res, h => by
    obtain ⟨e1, e2, e3, e4, e5, e6, hOk, -⟩ := h
    refine ⟨rfl, fun i hi ↦ ?_, e5, e6, ⟨_, hOk⟩, fun i hi ↦ absurd hi (by simp)⟩
    obtain rfl : i = 0 := by simpa using hi
    exact ⟨⟨R, _, hOk⟩, by simpa using e2, e1, by simpa using e3, by simp [e4]⟩
  | level :: next :: cfg, lvl, ws, F, xs, os, R, L :: Ls, res, h => by
    obtain ⟨e1, e2, e3, e4, e5, e6, d, xsR, osR, hOk, -, -, h'⟩ := h
    obtain ⟨hl, hat, hws, hF, hok0, hnext⟩ := chain_at (next :: cfg) (lvl + 1) _ _ xsR osR _ Ls res h'
    have hne : Ls ≠ [] := by intro h; rw [h] at hl; simp at hl
    refine ⟨by simp [hl], fun i hi ↦ ?_, e5, e6, ⟨d, hOk⟩, fun i hi ↦ ?_⟩
    · rcases i with _ | i
      · refine ⟨⟨R, d, hOk⟩, by simpa using e2, e1, by simpa using e3, ?_⟩
        simp only [List.getD_cons_zero, e4, Bool.false_eq_true, false_iff, List.length_cons]
        have := List.length_pos_of_ne_nil hne
        omega
      · have hi' : i < Ls.length := by simpa using hi
        have := hat i hi'
        simp only [List.getD_cons_succ, List.length_cons]
        exact ⟨this.ok, by rw [this.index]; ring, this.logN, by simpa using this.level,
          by rw [this.fin]; omega⟩
    · rcases i with _ | i
      · simp only [List.getD_cons_succ, List.getD_cons_zero]
        exact ⟨hws, hF⟩
      · simpa using hnext i (by simpa using hi)
  | [], _, _, _, _, _, _, _, _, h => by simp [SpChain] at h
  | [_], _, _, _, _, _, _, [], _, h => by simp [SpChain] at h
  | [_], _, _, _, _, _, _, _ :: _ :: _, _, h => by simp [SpChain] at h
  | _ :: _ :: _, _, _, _, _, _, _, [], _, h => by simp [SpChain] at h

/-- **Each level after the first opens the commitment the previous one read.** -/
theorem chain_roots : ∀ (cfg : List Whir.Level) (lvl : ℕ) (ws : WhirStateT) (F : Fs) (xs : List E)
    (os : List (List Opening)) (R : List (Digest × ℕ × ℕ)) (Ls : List SpLv) (res : WhirEnd × FSt),
    SpChain logN lane lvl cfg ws F xs os R Ls res → R.length = lvl + 1 →
    ∀ i, i + 1 < Ls.length → (Ls.getD (i + 1) default).root = (Ls.getD i default).dn
  | [level], lvl, ws, F, xs, os, R, [L], res, _, _, i, hi => absurd hi (by simp)
  | level :: next :: cfg, lvl, ws, F, xs, os, R, L :: Ls, res, h, hR, i, hi => by
    obtain ⟨e1, e2, e3, e4, e5, e6, d, xsR, osR, hOk, -, -, h'⟩ := h
    rcases i with _ | i
    · obtain ⟨-, hat, -, -, ⟨d', hok'⟩, -⟩ := chain_at _ _ _ _ _ _ _ _ _ h'
      have hr := hok'.root
      have hidx := (hat 0 (by
        have := (chain_at _ _ _ _ _ _ _ _ _ h').1; simp [this])).index
      rw [hidx, Nat.add_zero, List.getElem?_append_right (by rw [hR])] at hr
      simp only [hR, Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hr
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [← hr.1]
      have hd := hOk.digest e4
      rw [SpLv.dn, hd]; rfl
    · simp only [List.getD_cons_succ]
      exact chain_roots _ _ _ _ _ _ _ Ls res h' (by simp [hR]) i (by simpa using hi)
  | [], _, _, _, _, _, _, _, _, h, _, _, _ => by simp [SpChain] at h
  | [_], _, _, _, _, _, _, [], _, h, _, _, _ => by simp [SpChain] at h
  | [_], _, _, _, _, _, _, _ :: _ :: _, _, h, _, _, _ => by simp [SpChain] at h
  | _ :: _ :: _, _, _, _, _, _, _, [], _, h, _, _, _ => by simp [SpChain] at h

/-- **Every level's fold challenges are a prefix of the last level's.** -/
theorem chain_folds : ∀ (cfg : List Whir.Level) (lvl : ℕ) (ws : WhirStateT) (F : Fs) (xs : List E)
    (os : List (List Opening)) (R : List (Digest × ℕ × ℕ)) (Ls : List SpLv) (res : WhirEnd × FSt),
    SpChain logN lane lvl cfg ws F xs os R Ls res →
    ∀ i < Ls.length, (Ls.getD i default).wsEnd.folds <+: (Ls.getLastD default).wsEnd.folds
  | [level], lvl, ws, F, xs, os, R, [L], res, _, i, hi => by
    obtain rfl : i = 0 := by simpa using hi
    exact List.prefix_refl _
  | level :: next :: cfg, lvl, ws, F, xs, os, R, L :: Ls, res, h, i, hi => by
    obtain ⟨-, -, -, -, -, -, d, xsR, osR, -, -, -, h'⟩ := h
    obtain ⟨hl, -, hws, -, -, -⟩ := chain_at _ _ _ _ _ _ _ _ _ h'
    have hne : Ls ≠ [] := by intro h; rw [h] at hl; simp at hl
    have hlast : (L :: Ls).getLastD default = Ls.getLastD default := by
      cases Ls with
      | nil => exact absurd rfl hne
      | cons _ _ => rfl
    rw [hlast]
    rcases i with _ | i
    · have h0 := chain_folds _ _ _ _ _ _ _ Ls res h' 0 (List.length_pos_of_ne_nil hne)
      refine List.IsPrefix.trans ?_ h0
      simp only [List.getD_cons_zero]
      rw [SpLv.wsEnd_folds (Ls.getD 0 default), hws]
      exact List.prefix_append _ _
    · simpa using chain_folds _ _ _ _ _ _ _ Ls res h' i (by simpa using hi)
  | [], _, _, _, _, _, _, _, _, h, _, _ => by simp [SpChain] at h
  | [_], _, _, _, _, _, _, [], _, h, _, _ => by simp [SpChain] at h
  | [_], _, _, _, _, _, _, _ :: _ :: _, _, h, _, _ => by simp [SpChain] at h
  | _ :: _ :: _, _, _, _, _, _, _, [], _, h, _, _ => by simp [SpChain] at h

end
end LeanVM.Guest.B1.Whir
