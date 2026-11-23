/-
  LeanVM.Guest.B1.Opening.QueriesPops

  The witness-stream entries `opening_queries` and its loop helpers pop: each query its row
  (`merkle_leaf_rows`), then its inline walk's siblings (`merkle_children`).
-/

module

public import LeanVM.Guest.B1.Opening.WalkPops

/-!
# `opening_queries`' pops

A query (`oqQueryT`), its windows' words arms of their matches (`WinSel`), pops its row's cells,
one `merkle_leaf_rows` entry (`rowPop`), then its siblings' cells, one `merkle_children` entry
(`queryPops`); nothing else in the function or its loop helper is a witness hint.

* `oqQuery_fallPops`: a query;
* `oqLoop1_pops`, `oqLoop0_pops`: a loop helper's call instance pops its queries' entries, then its
  next iteration's;
* `oqMain_pops`: the function's call instance pops, at level 0 when `odd_g + 1 ≠ 0`, its odd first
  query's entries, then its loop's.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## No other hints -/

theorem oqPacksT_noWit (b I : ℕ) : noWit (oqPacksT b I) = true := noWit_flatten_map fun _ _ => rfl

theorem oqXorT_noWit (s : Oq) (b pr kL k c : ℕ) : noWit (oqXorT s b pr kL k c) = true := by
  unfold oqXorT; dsimp only; split_ifs <;> rfl

theorem oqBlockT_noWit (s : Oq) (b pr kL k : ℕ) : noWit (oqBlockT s b pr kL k) = true := by
  unfold oqBlockT
  split_ifs
  · rfl
  · rw [noWit_append, noWit_flatten_map fun c _ => oqXorT_noWit s b pr kL k c]; rfl

theorem oqLeafT_noWit (s : Oq) (b pr kL : ℕ) : noWit (oqLeafT s b pr kL) = true :=
  noWit_flatten_map fun _ _ => oqBlockT_noWit _ _ _ _ _

theorem oqRoundT_noWit (s : Oq) (coefs x : V) (b F j : ℕ) : noWit (oqRoundT s coefs x b F j) = true := by
  unfold oqRoundT; dsimp only
  rw [noWit_append, noWit_flatten_map fun _ _ => rfl]; rfl

theorem oqFoldT_noWit (s : Oq) (coefs x : V) (b F : ℕ) : noWit (oqFoldT s coefs x b F) = true :=
  noWit_flatten_map fun _ _ => oqRoundT_noWit _ _ _ _ _ _

theorem nvLevelT_noWit (w : V) : ∀ (ins : List ℕ) (k : ℕ), noWit (nvLevelT w ins k).1 = true
  | _ :: _ :: rest, k => by
    simp only [nvLevelT]; rw [noWit_append, nvLevelT_noWit w rest (k + 2)]; rfl
  | [_], _ => rfl
  | [], _ => rfl

theorem nvLevelsT_noWit (ws : ℕ → ℕ) : ∀ (c i : ℕ) (ins : List ℕ) (k : ℕ), noWit (nvLevelsT ws c i ins k).1 = true
  | 0, _, _, _ => rfl
  | c + 1, i, ins, k => by
    simp only [nvLevelsT]; rw [noWit_append, nvLevelT_noWit, nvLevelsT_noWit ws c]; rfl

theorem oqFinT_noWit (s : Oq) (x hs : V) (v : ℕ) : noWit (oqFinT s x hs v) = true := by
  have h1 : noWit (oqWsT s x v) = true := by
    unfold oqWsT; simp only [noWit_append, Bool.and_eq_true]; exact ⟨rfl, noWit_flatten_map fun _ _ => rfl⟩
  have h2 : noWit (oqNovel s hs v).1 = true := by
    unfold oqNovel nvLevel0T; dsimp only
    simp only [noWit_append, Bool.and_eq_true]; exact ⟨noWit_flatten_map fun _ _ => rfl, nvLevelsT_noWit _ _ _ _ _⟩
  unfold oqFinT; simp only [noWit_append, Bool.and_eq_true]; exact ⟨⟨h1, h2⟩, rfl⟩

/-! ## Calls -/

/-! ## A query -/

/-- **A query's row**: its `I` cells from `b`, one `merkle_leaf_rows` entry. -/
def rowPop (σ : Val) (b I : ℕ) : Pop := ("merkle_leaf_rows", (List.range I).map fun j => σ (.n (b + j)))

/-- **A query's entries**: its row, then its siblings' `2·pd` cells from `oqCh`. -/
def queryPops (σ : Val) (s : Oq) (b : ℕ) (emit : Bool) : List Pop :=
  [rowPop σ b s.I, ("merkle_children", (List.range (2 * s.pd)).map fun j ↦ σ (.n (oqCh s b emit + j)))]

/-- The windows' words of a walk from `ch` are arms of their matches. -/
def WinSel (σ : Val) (s : Oq) (ch : ℕ) : Prop :=
  ∀ i < oqNpw s, ∃ k < 2 ^ oqWw s i, σ (.n (oqWk s ch i)) = ofK (addressOfIndex k)

/-- **A query pops its row's cells, then its siblings' cells.** -/
theorem oqQuery_fallPops (s : Oq) (x bp cap flags coefs hs : V) (b : ℕ) (emit : Bool) (pr : ℕ)
    (hsel : WinSel σ s (oqCh s b emit)) :
    FallPops rd σ (oqQueryT s x bp cap flags coefs hs b emit pr) (queryPops σ s b emit) := by
  have hrow : FallPops rd σ (oqPrepT s b) [rowPop σ b s.I] := by
    refine fallPops_eq ((FallPops.atom _).append (fallPops_noWit σ (ss := if s.base = 1 then oqPacksT b s.I else [])
      (by split; exacts [oqPacksT_noWit _ _, rfl]))) ?_
    simp [Atom.pops, Hint.pops, Dest.words, rowPop]
  have hpad : noWit (if emit then oqPadT (oqK1 s b) else []) = true := by split <;> rfl
  have hfin : noWit (if s.final = 1 then oqFinT s x hs (oqVal s (oqFo s b emit)) else []) = true := by
    split; exacts [oqFinT_noWit _ _ _ _, rfl]
  refine fallPops_eq (((((hrow.append (fallPops_noWit σ hpad)).append
    (fallPops_noWit σ (oqLeafT_noWit s b (oqPr s b emit pr) (oqKL s b emit)))).append
    (oqWalkT_fallPops (bp := bp) (cap := cap) (flags := flags) (pr := oqPr s b emit pr)
      (kN := oqDig s b emit) hsel)).append (fallPops_noWit σ (oqFoldT_noWit s coefs x b (oqFo s b emit)))).append
    (fallPops_noWit σ hfin)) ?_
  simp [queryPops]

/-! ## The loop helpers -/

theorem oqLoop1A_fallPops (s : Oq) (h1 : WinSel σ s (oqCh s 15 true))
    (h2 : WinSel σ s (oqCh s (oqE1 s + 2) false)) :
    FallPops rd σ (oqLoop1A s) (queryPops σ s 15 true ++ queryPops σ s (oqE1 s + 2) false) := by
  have htail : noWit ((if s.final = 1 then [] else
      [.atom (.mul (.n (oqC1 s)) (.n oqChainP) (.n oqX)), .atom (.load (.n (oqC1 s + 1)) (.n (oqC1 s)) 0),
        .atom (.add (.n (oqC1 s + 2)) (.n (oqC1 s + 1)) (.n (oqRes s 15 true))),
        .atom (.mul (.n (oqC1 s + 3)) (.n (oqC1 s + 2)) (.n oqLamInv)),
        .atom (.add (.n (oqC1 s + 4)) (.n (oqC1 s + 3)) (.n (oqRes s (oqE1 s + 2) false))),
        .atom (.mul (.n (oqC1 s + 5)) (.n (oqC1 s + 4)) (.n oqLamInv)),
        .atom (.mul (.n (oqC1 s + 6)) (.n oqChainP) (.n oqX)),
        .atom (.load (.n (oqC1 s + 5)) (.n (oqC1 s + 6)) 1)]) ++ oqGuardA (oqG1 s)) = true := by
    rw [noWit_append]; split <;> rfl
  have h := ((((fallPops_noWit (rd := rd) σ (ss := [.atom (.mul (.n 10) (.n oqX) (.n oqX)),
      .atom (.mul (.n 11) (.n oqPos) (.n 10)), .atom (.mul (.n 12) (.n oqQp) (.n 10)),
      .atom (.load (.n 13) (.n 11) 0), .atom (.load (.n 14) (.n 12) 0)]) rfl).append
    (oqQuery_fallPops s (.n 13) (.n 14) (.n oqCap) (.n oqFlags) (.n oqCoefs) (.n oqHs) 15 true 0 h1)).append
    (fallPops_noWit σ (ss := [.atom (.load (.n (oqE1 s)) (.n 11) 1),
      .atom (.load (.n (oqE1 s + 1)) (.n 12) 1)]) rfl)).append
    (oqQuery_fallPops s (.n (oqE1 s)) (.n (oqE1 s + 1)) (.n oqCap) (.n oqFlags) (.n oqCoefs) (.n oqHs)
      (oqE1 s + 2) false (oqK1 s 15) h2)).append (fallPops_noWit σ htail)
  simp only [List.append_assoc, List.nil_append, List.append_nil] at h
  simpa only [oqLoop1A, List.append_assoc] using h

theorem oqLoop0A_fallPops (s : Oq) (h1 : WinSel σ s (oqCh s 14 true)) :
    FallPops rd σ (oqLoop0A s) (queryPops σ s 14 true) := by
  have htail : noWit ((if s.final = 1 then [] else
      [.atom (.mul (.n (oqC0 s)) (.n oqChainP) (.n oqX)), .atom (.load (.n (oqC0 s + 1)) (.n (oqC0 s)) 0),
        .atom (.add (.n (oqC0 s + 2)) (.n (oqC0 s + 1)) (.n (oqRes s 14 true))),
        .atom (.mul (.n (oqC0 s + 3)) (.n (oqC0 s + 2)) (.n oqLamInv)),
        .atom (.mul (.n (oqC0 s + 4)) (.n oqChainP) (.n oqX)),
        .atom (.load (.n (oqC0 s + 3)) (.n (oqC0 s + 4)) 1)]) ++ oqGuardA (oqG0 s)) = true := by
    rw [noWit_append]; split <;> rfl
  have h := ((fallPops_noWit (rd := rd) σ (ss := [.atom (.mul (.n 10) (.n oqPos) (.n oqX)),
      .atom (.load (.n 11) (.n 10) 0), .atom (.mul (.n 12) (.n oqQp) (.n oqX)),
      .atom (.load (.n 13) (.n 12) 0)]) rfl).append
    (oqQuery_fallPops s (.n 11) (.n 13) (.n oqCap) (.n oqFlags) (.n oqCoefs) (.n oqHs) 14 true 0 h1)).append
    (fallPops_noWit σ htail)
  simp only [List.append_assoc, List.nil_append, List.append_nil] at h
  simpa only [oqLoop0A, List.append_assoc] using h

/-- **A level-0 iteration pops its two queries' entries, then its next iteration's.** -/
theorem oqLoop1_pops {P : Core.Program} {name : String} {fn : Fn} (hf : P.find? name = some fn) {s : Oq}
    (hb : fn.body = oqLoop1T s name) (τ : Val) (bufs : List ℕ)
    (h1 : WinSel τ s (oqCh s 15 true)) (h2 : WinSel τ s (oqCh s (oqE1 s + 2) false))
    {kids : List Tree} {kn : List Pop} (hk : Tree.popsKids P rd kids = [kn]) :
    (Memory.Tree.node name τ bufs kids).pops P rd =
      queryPops τ s 15 true ++ queryPops τ s (oqE1 s + 2) false ++ kn := by
  have hx : SplicePops rd τ (oqLoop1A s ++ [.callIf (.n (oqG1 s + 2)) name (oqNextArgs (oqG1 s))])
      (Tree.popsKids P rd kids) (queryPops τ s 15 true ++ queryPops τ s (oqE1 s + 2) false ++ kn) := by
    rw [hk]
    exact SplicePops.congr_ks ((SplicePops.of_fallPops (oqLoop1A_fallPops s h1 h2)).append
      (SplicePops.callIf _ _ _ kn)) rfl
  obtain ⟨es, -, he⟩ := Tree.pops_of_splice (bufs := bufs) hf
    (ys := [.ret []]) (by rw [hb, oqLoop1T, oqNextT_eq]; simp) hx (es := []) (vs := [])
    (by simp [walk, walk1, Out.seq]) rfl
  rw [he]; simp [evPops]

/-- **A deeper iteration pops its query's entries, then its next iteration's.** -/
theorem oqLoop0_pops {P : Core.Program} {name : String} {fn : Fn} (hf : P.find? name = some fn) {s : Oq}
    (hb : fn.body = oqLoop0T s name) (τ : Val) (bufs : List ℕ) (h1 : WinSel τ s (oqCh s 14 true))
    {kids : List Tree} {kn : List Pop} (hk : Tree.popsKids P rd kids = [kn]) :
    (Memory.Tree.node name τ bufs kids).pops P rd = queryPops τ s 14 true ++ kn := by
  have hx : SplicePops rd τ (oqLoop0A s ++ [.callIf (.n (oqG0 s + 2)) name (oqNextArgs (oqG0 s))])
      (Tree.popsKids P rd kids) (queryPops τ s 14 true ++ kn) := by
    rw [hk]
    exact SplicePops.congr_ks ((SplicePops.of_fallPops (oqLoop0A_fallPops s h1)).append
      (SplicePops.callIf _ _ _ kn)) rfl
  obtain ⟨es, -, he⟩ := Tree.pops_of_splice (bufs := bufs) hf
    (ys := [.ret []]) (by rw [hb, oqLoop0T, oqNextT_eq]; simp) hx (es := []) (vs := [])
    (by simp [walk, walk1, Out.seq]) rfl
  rw [he]; simp [evPops]

/-! ## The function -/

/-- The start's entries: at level 0 when `odd_g + 1 ≠ 0`, the odd first query's. -/
def startPops (σ : Val) (s : Oq) : List Pop :=
  if s.base = 1 ∧ σ (.n 13) ≠ 0 then queryPops σ s 17 true else []

theorem oqMainA_fallPops (s : Oq) (hodd : s.base = 1 → σ (.n 13) ≠ 0 → WinSel σ s (oqCh s 17 true)) :
    FallPops rd σ (oqMainA s) (startPops σ s) := by
  by_cases hb : s.base = 1
  · rw [oqMainA_one hb]
    have hodd' : σ (.n 13) ≠ 0 → FallPops rd σ (oqOddT s) (queryPops σ s 17 true) := fun h0 =>
      fallPops_eq (((fallPops_noWit (rd := rd) σ (ss := [.atom (.load (.n 15) (.n oqMPos) 0),
        .atom (.load (.n 16) (.n oqMQp) 0)]) rfl).append (oqQuery_fallPops s (.n 15) (.n 16) (.n oqMCap)
        (.n oqMFlags) (.n oqMCoefs) (.n oqMHs) 17 true 0 (hodd hb h0))).append
        (fallPops_noWit σ (ss := [.atom (.mul (.n (oqEnd s 17 true)) (.n (oqRes s 17 true)) (.n oqMLamInv)),
          .atom (.load (.n (oqEnd s 17 true)) (.n 11) 0)]) rfl)) (by simp)
    have hite : FallPops rd σ [.ite (.n 13) oqEvenT (oqOddT s)]
        (if σ (.n 13) = 0 then [] else queryPops σ s 17 true) := by
      refine FallPops.ite ?_
      by_cases h0 : σ (.n 13) = 0
      · rw [ite_eq_left h0, ite_eq_left h0]; exact fallPops_noWit σ rfl
      · rw [ite_eq_right h0, ite_eq_right h0]; exact hodd' h0
    refine fallPops_eq (((fallPops_noWit σ (ss := oqMainPre) rfl).append hite).append
      (fallPops_noWit σ (ss := oqMainPost s) rfl)) ?_
    by_cases h0 : σ (.n 13) = 0 <;> simp [startPops, hb, h0]
  · refine fallPops_eq (fallPops_noWit σ ?_) (by simp [startPops, hb])
    simp [oqMainA, hb]; rfl

/-- **`opening_queries` pops its odd first query's entries, then its loop's.** -/
theorem oqMain_pops {P : Core.Program} {name : String} {fn : Fn} (hf : P.find? name = some fn) {s : Oq}
    {loop : String} (hb : fn.body = oqMainT s loop) (τ : Val) (bufs : List ℕ)
    (hodd : s.base = 1 → τ (.n 13) ≠ 0 → WinSel τ s (oqCh s 17 true))
    {kids : List Tree} {kl : List Pop} (hk : Tree.popsKids P rd kids = [kl]) :
    (Memory.Tree.node name τ bufs kids).pops P rd = startPops τ s ++ kl := by
  have hx : SplicePops rd τ (oqMainA s ++ [.callIf (.n (oqMK s + 1)) loop
      [.n (oqMK s + 2), .n oqMN, .n (if s.base = 1 then oqMK s - 2 else oqMPos),
        .n (if s.base = 1 then oqMK s - 1 else oqMQp), .n oqMCap, .n oqMFlags, .n oqMCoefs, .n oqMHs, .n 11,
        .n oqMLamInv]]) (Tree.popsKids P rd kids) (startPops τ s ++ kl) := by
    rw [hk]
    exact SplicePops.congr_ks ((SplicePops.of_fallPops (oqMainA_fallPops s hodd)).append
      (SplicePops.callIf _ _ _ kl)) rfl
  have hy : ∃ es vs, walk τ (if s.final = 1 then [.atom (.const (.n (oqMK s + 3)) (word 0 0)),
      .ret [.n (oqMK s + 3)]] else [.atom (.mul (.n (oqMK s + 3)) (.n 11) (.n oqMN)),
      .atom (.load (.n (oqMK s + 4)) (.n (oqMK s + 3)) 0), .atom (.copy (.n (oqMK s + 5))
      (.n (oqMK s + 4))), .ret [.n (oqMK s + 5)]]) = .ret es vs ∧ calls es = [] ∧ evPops rd τ es = [] := by
    split
    · exact ⟨[.atom (.const (.n (oqMK s + 3)) (word 0 0))], [.n (oqMK s + 3)],
        by simp [walk, walk1, Out.seq, Out.pre], rfl, rfl⟩
    · exact ⟨[.atom (.mul (.n (oqMK s + 3)) (.n 11) (.n oqMN)),
        .atom (.load (.n (oqMK s + 4)) (.n (oqMK s + 3)) 0),
        .atom (.copy (.n (oqMK s + 5)) (.n (oqMK s + 4)))], [.n (oqMK s + 5)],
        by simp [walk, walk1, Out.seq, Out.pre], rfl, rfl⟩
  obtain ⟨es, vs, hw, hc, hp⟩ := hy
  obtain ⟨es', -, he⟩ := Tree.pops_of_splice (bufs := bufs) hf
    (by rw [hb, oqMainT, List.append_assoc]) hx hw hc
  rw [he, hp, List.append_nil]

end
end LeanVM.Guest.B1
