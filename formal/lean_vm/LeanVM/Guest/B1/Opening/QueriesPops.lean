/-
  LeanVM.Guest.B1.Opening.QueriesPops

  The witness-stream entries `opening_queries` and its loop helpers pop: each query its row (`merkle_leaf_rows`), its `walk_path` call's spliced in.
-/

module

public import LeanVM.Guest.B1.Opening.WalkPops

/-!
# `opening_queries`' pops

Whatever the valuation, a query (`oqQueryT`) pops its row's cells, one `merkle_leaf_rows` entry (`rowPop`), then its `walk_path` call's entries; nothing else in the function or its loop helper is a witness hint.

* `oqQuery_splicePops`: a query, its walk's entries `k` spliced in;
* `oqLoop1_pops`, `oqLoop0_pops`: a loop helper's call instance pops its queries' rows, its walks' entries and its next iteration's;
* `oqMain_pops`: the function's call instance pops its odd first query's row and walk's entries, then its loop's.
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

/-- **A query pops its row's cells, then its walk's entries.** -/
theorem oqQuery_splicePops (s : Oq) (x bp cap flags coefs hs : V) (b : ℕ) (emit : Bool) (pr : ℕ)
    (walk : String) (k : List Pop) :
    SplicePops rd σ (oqQueryT s x bp cap flags coefs hs b emit pr walk) [k] (rowPop σ b s.I :: k) := by
  have hrow : FallPops rd σ (oqPrepT s b) [rowPop σ b s.I] := by
    refine fallPops_eq ((FallPops.atom _).append (fallPops_noWit σ (ss := if s.base = 1 then oqPacksT b s.I else [])
      (by split; exacts [oqPacksT_noWit _ _, rfl]))) ?_
    simp [Atom.pops, Hint.pops, Dest.words, rowPop]
  have hpad : noWit (if emit then oqPadT (oqK1 s b) else []) = true := by split <;> rfl
  have hfin : noWit (if s.final = 1 then oqFinT s x hs (oqVal s (oqCh s b emit)) else []) = true := by
    split; exacts [oqFinT_noWit _ _ _ _, rfl]
  have h := SplicePops.congr_pops (SplicePops.congr_ks ((((((SplicePops.of_fallPops hrow).append
    (splicePops_noWit hpad)).append (splicePops_noWit (oqLeafT_noWit s b (oqPr s b emit pr) (oqKL s b emit)))).append
    (SplicePops.call walk [.n (oqOut s (oqKL s b emit) (s.B - 1) 0), .n (oqOut s (oqKL s b emit) (s.B - 1) 1), bp,
      cap, flags] [] k)).append (splicePops_noWit (oqFoldT_noWit s coefs x b (oqCh s b emit)))).append
    (splicePops_noWit hfin)) (ks' := [k]) (by simp)) (q := rowPop σ b s.I :: k) (by simp)
  simp only [List.append_assoc] at h
  simpa only [oqQueryT, List.append_assoc] using h

/-! ## The loop helpers -/

theorem oqGuardA_noWit (g : ℕ) : noWit (oqGuardA g) = true := rfl

theorem oqLoop1A_splicePops (s : Oq) (odd : ℕ) (walk : String) (k1 k2 : List Pop) :
    SplicePops rd σ (oqLoop1A s odd walk) [k1, k2] (rowPop σ 16 s.I :: k1 ++ rowPop σ (oqE1 s + 2) s.I :: k2) := by
  have htail : noWit ((if s.final = 1 then [] else
      [.atom (.mul (.n (oqC1 s)) (.n 8) (.n 0)), .atom (.load (.n (oqC1 s + 1)) (.n (oqC1 s)) 0),
        .atom (.add (.n (oqC1 s + 2)) (.n (oqC1 s + 1)) (.n (oqRes s 16 true))),
        .atom (.mul (.n (oqC1 s + 3)) (.n (oqC1 s + 2)) (.n 9)),
        .atom (.add (.n (oqC1 s + 4)) (.n (oqC1 s + 3)) (.n (oqRes s (oqE1 s + 2) false))),
        .atom (.mul (.n (oqC1 s + 5)) (.n (oqC1 s + 4)) (.n 9)), .atom (.mul (.n (oqC1 s + 6)) (.n 8) (.n 0)),
        .atom (.load (.n (oqC1 s + 5)) (.n (oqC1 s + 6)) 1)]) ++ oqGuardA (oqG1 s)) = true := by
    rw [noWit_append]; split <;> rfl
  have h := ((((splicePops_noWit (rd := rd) (σ := σ) (ss := [.atom (.mul (.n 10) (.n 2) (.n 0)),
      .atom (.mul (.n 11) (.n 10) (.n 0)), .atom (.mul (.n 12) (.n 3) (.n 0)), .atom (.mul (.n 13) (.n 12) (.n 0)),
      .atom (.load (.n 14) (.n 11) odd), .atom (.load (.n 15) (.n 13) odd)]) rfl).append
    (oqQuery_splicePops s (.n 14) (.n 15) (.n 4) (.n 5) (.n 6) (.n 7) 16 true 0 walk k1)).append
    (splicePops_noWit (ss := [.atom (.load (.n (oqE1 s)) (.n 11) (odd + 1)),
      .atom (.load (.n (oqE1 s + 1)) (.n 13) (odd + 1))]) rfl)).append
    (oqQuery_splicePops s (.n (oqE1 s)) (.n (oqE1 s + 1)) (.n 4) (.n 5) (.n 6) (.n 7) (oqE1 s + 2) false
      (oqK1 s 16) walk k2)).append (splicePops_noWit htail)
  have h' := SplicePops.congr_pops (SplicePops.congr_ks h (ks' := [k1, k2]) (by simp))
    (q := rowPop σ 16 s.I :: k1 ++ rowPop σ (oqE1 s + 2) s.I :: k2) (by simp)
  simp only [List.append_assoc] at h'
  simpa only [oqLoop1A, List.append_assoc] using h'

theorem oqLoop0A_splicePops (s : Oq) (walk : String) (k : List Pop) :
    SplicePops rd σ (oqLoop0A s walk) [k] (rowPop σ 14 s.I :: k) := by
  have htail : noWit ((if s.final = 1 then [] else
      [.atom (.mul (.n (oqC0 s)) (.n 8) (.n 0)), .atom (.load (.n (oqC0 s + 1)) (.n (oqC0 s)) 0),
        .atom (.add (.n (oqC0 s + 2)) (.n (oqC0 s + 1)) (.n (oqRes s 14 true))),
        .atom (.mul (.n (oqC0 s + 3)) (.n (oqC0 s + 2)) (.n 9)), .atom (.mul (.n (oqC0 s + 4)) (.n 8) (.n 0)),
        .atom (.load (.n (oqC0 s + 3)) (.n (oqC0 s + 4)) 1)]) ++ oqGuardA (oqG0 s)) = true := by
    rw [noWit_append]; split <;> rfl
  have h := ((splicePops_noWit (rd := rd) (σ := σ) (ss := [.atom (.mul (.n 10) (.n 2) (.n 0)),
      .atom (.load (.n 11) (.n 10) 0), .atom (.mul (.n 12) (.n 3) (.n 0)), .atom (.load (.n 13) (.n 12) 0)]) rfl).append
    (oqQuery_splicePops s (.n 11) (.n 13) (.n 4) (.n 5) (.n 6) (.n 7) 14 true 0 walk k)).append
    (splicePops_noWit htail)
  have h' := SplicePops.congr_pops (SplicePops.congr_ks h (ks' := [k]) (by simp)) (q := rowPop σ 14 s.I :: k)
    (by simp)
  simp only [List.append_assoc] at h'
  simpa only [oqLoop0A, List.append_assoc] using h'

/-- **A level-0 iteration pops its two queries' rows and walks' entries, then its next iteration's.** -/
theorem oqLoop1_pops {P : Core.Program} {name : String} {fn : Fn} (hf : P.find? name = some fn) {s : Oq}
    {odd : ℕ} {wlk : String} (hb : fn.body = oqLoop1T s odd wlk name) (τ : Val) (bufs : List ℕ)
    {kids : List Tree} {k1 k2 kn : List Pop} (hk : Tree.popsKids P rd kids = [k1, k2, kn]) :
    (Memory.Tree.node name τ bufs kids).pops P rd =
      rowPop τ 16 s.I :: k1 ++ rowPop τ (oqE1 s + 2) s.I :: k2 ++ kn := by
  have hx : SplicePops rd τ (oqLoop1A s odd wlk ++ [.callIf (.n (oqG1 s + 2)) name
      [.n (oqG1 s + 4), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9]]) (Tree.popsKids P rd kids)
      (rowPop τ 16 s.I :: k1 ++ rowPop τ (oqE1 s + 2) s.I :: k2 ++ kn) := by
    rw [hk]; exact (oqLoop1A_splicePops s odd wlk k1 k2).append (SplicePops.callIf _ _ _ kn)
  obtain ⟨es, -, he⟩ := Tree.pops_of_splice (bufs := bufs) hf
    (ys := [.ret []]) (by simp [hb, oqLoop1T, oqNextT]) hx (es := []) (vs := [])
    (by simp [walk, walk1, Out.seq]) rfl
  rw [he]; simp [evPops]

/-- **A deeper iteration pops its query's row and walk's entries, then its next iteration's.** -/
theorem oqLoop0_pops {P : Core.Program} {name : String} {fn : Fn} (hf : P.find? name = some fn) {s : Oq}
    {wlk : String} (hb : fn.body = oqLoop0T s wlk name) (τ : Val) (bufs : List ℕ)
    {kids : List Tree} {k kn : List Pop} (hk : Tree.popsKids P rd kids = [k, kn]) :
    (Memory.Tree.node name τ bufs kids).pops P rd = rowPop τ 14 s.I :: k ++ kn := by
  have hx : SplicePops rd τ (oqLoop0A s wlk ++ [.callIf (.n (oqG0 s + 2)) name
      [.n (oqG0 s + 4), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9]]) (Tree.popsKids P rd kids)
      (rowPop τ 14 s.I :: k ++ kn) := by
    rw [hk]; exact (oqLoop0A_splicePops s wlk k).append (SplicePops.callIf _ _ _ kn)
  obtain ⟨es, -, he⟩ := Tree.pops_of_splice (bufs := bufs) hf
    (ys := [.ret []]) (by simp [hb, oqLoop0T, oqNextT]) hx (es := []) (vs := [])
    (by simp [walk, walk1, Out.seq]) rfl
  rw [he]; simp [evPops]

/-! ## The function -/

theorem oqMainA_splicePops (s : Oq) (odd : ℕ) (walk : String) (ks : List (List Pop)) (p : List Pop)
    (h : if odd = 1 then ∃ k, ks = [k] ∧ p = rowPop σ 13 s.I :: k else ks = [] ∧ p = []) :
    SplicePops rd σ (oqMainA s odd walk) ks p := by
  have hhead : noWit [.atom (.const (.n 8) (word 2 0)), .atom (.mul (.n 9) (.n 7) (.n 8)),
      .atom (.hint (.allocDyn (.n 10) (.n 9)))] = true := rfl
  have htail : noWit [.atom (.const (.n (oqMK s odd)) (word 1 0)), .atom (.add (.n (oqMK s odd + 1))
      (.n (oqMK s odd)) (.n 7)), .atom (.const (.n (oqMK s odd + 2)) (word 1 0))] = true := rfl
  have hmid : SplicePops rd σ (if odd = 1 then
      [.atom (.load (.n 11) (.n 5) 0), .atom (.load (.n 12) (.n 6) 0)] ++
        oqQueryT s (.n 11) (.n 12) (.n 0) (.n 1) (.n 3) (.n 4) 13 true 0 walk ++
        [.atom (.mul (.n (oqMK s odd - 1)) (.n (oqRes s 13 true)) (.n 2)),
          .atom (.load (.n (oqMK s odd - 1)) (.n 10) 0)]
      else [.atom (.const (.n 11) (word 0 0)), .atom (.load (.n 11) (.n 10) 0)]) ks p := by
    split_ifs at h ⊢
    · obtain ⟨k, rfl, rfl⟩ := h
      exact SplicePops.congr_pops (SplicePops.congr_ks (((splicePops_noWit rfl).append
        (oqQuery_splicePops s (.n 11) (.n 12) (.n 0) (.n 1) (.n 3) (.n 4) 13 true 0 walk k)).append
        (splicePops_noWit rfl)) (by simp)) (by simp)
    · obtain ⟨rfl, rfl⟩ := h
      exact splicePops_noWit rfl
  have h := SplicePops.congr_pops (SplicePops.congr_ks (((splicePops_noWit hhead).append hmid).append
    (splicePops_noWit htail)) (ks' := ks) (by simp)) (q := p) (by simp)
  simpa only [oqMainA, List.append_assoc] using h

/-- **`opening_queries` pops its odd first query's row and walk's entries, then its loop's.** -/
theorem oqMain_pops {P : Core.Program} {name : String} {fn : Fn} (hf : P.find? name = some fn) {s : Oq}
    {odd : ℕ} {wlk loop : String} (hb : fn.body = oqMainT s odd wlk loop) (τ : Val) (bufs : List ℕ)
    {kids : List Tree} {ks : List (List Pop)} {p kl : List Pop}
    (hodd : if odd = 1 then ∃ k, ks = [k] ∧ p = rowPop τ 13 s.I :: k else ks = [] ∧ p = [])
    (hk : Tree.popsKids P rd kids = ks ++ [kl]) :
    (Memory.Tree.node name τ bufs kids).pops P rd = p ++ kl := by
  have hx : SplicePops rd τ (oqMainA s odd wlk ++ [.callIf (.n (oqMK s odd + 1)) loop
      [.n (oqMK s odd + 2), .n 7, .n 5, .n 6, .n 0, .n 1, .n 3, .n 4, .n 10, .n 2]]) (Tree.popsKids P rd kids)
      (p ++ kl) := by
    rw [hk]; exact (oqMainA_splicePops s odd wlk ks p hodd).append (SplicePops.callIf _ _ _ kl)
  have hy : ∃ es vs, walk τ (if s.final = 1 then [.atom (.const (.n (oqMK s odd + 3)) (word 0 0)),
      .ret [.n (oqMK s odd + 3)]] else [.atom (.mul (.n (oqMK s odd + 3)) (.n 10) (.n 7)),
      .atom (.load (.n (oqMK s odd + 4)) (.n (oqMK s odd + 3)) 0), .atom (.copy (.n (oqMK s odd + 5))
      (.n (oqMK s odd + 4))), .ret [.n (oqMK s odd + 5)]]) = .ret es vs ∧ calls es = [] ∧ evPops rd τ es = [] := by
    split
    · exact ⟨[.atom (.const (.n (oqMK s odd + 3)) (word 0 0))], [.n (oqMK s odd + 3)],
        by simp [walk, walk1, Out.seq, Out.pre], rfl, rfl⟩
    · exact ⟨[.atom (.mul (.n (oqMK s odd + 3)) (.n 10) (.n 7)),
        .atom (.load (.n (oqMK s odd + 4)) (.n (oqMK s odd + 3)) 0),
        .atom (.copy (.n (oqMK s odd + 5)) (.n (oqMK s odd + 4)))], [.n (oqMK s odd + 5)],
        by simp [walk, walk1, Out.seq, Out.pre], rfl, rfl⟩
  obtain ⟨es, vs, hw, hc, hp⟩ := hy
  obtain ⟨es', -, he⟩ := Tree.pops_of_splice (bufs := bufs) hf
    (by rw [hb, oqMainT, List.append_assoc]) hx hw hc
  rw [he, hp, List.append_nil]

end
end LeanVM.Guest.B1
