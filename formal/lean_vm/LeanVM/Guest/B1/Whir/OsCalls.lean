/-
  LeanVM.Guest.B1.Whir.OsCalls

  The frames `open_stacked`'s levels set up, level by level, and their callees placed.
-/

module

public import LeanVM.Guest.B1.Whir.OsKidsLv

/-!
# The levels' frames (TRIAGE #36)

`osLvsKOf`: per level, the frames before its positions, its query-position loop's, those after;
`os_levels_calls`: they are the levels' frames in order; `os_lvsK_ok`: under the levels' calls'
relations (`OsLvsCallsOk`) each level's are `OsLvKOk`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- Level `lvl`'s frames at `s`. -/
noncomputable def osLvKOf (cfg : OsCfg) (σ : Val) (lvl : ℕ) (s : OsSt) : OsLvK where
  A := (((osLvF cfg lvl s).1 ++ (osLvM cfg lvl s).1 ++ (osLvG cfg lvl s).1).filterMap Main.Stmt.callS).map (Main.mkCall σ)
  sq := Main.mkCall σ (some (.n ((osLvG cfg lvl s).2.k + 4)), (cfg.lv lvl).sqLoop,
    [.n ((osLvG cfg lvl s).2.k + 5), .n ((osLvG cfg lvl s).2.k + 6), .n ((osLvG cfg lvl s).2.k + 1), .n osQpos,
      .n osQbp], [])
  B := ((osLvRestB cfg lvl (osLvG cfg lvl s).2).filterMap Main.Stmt.callS).map (Main.mkCall σ)

/-- The levels' frames from level `lvl` at `s`, `n` of them. -/
noncomputable def osLvsKOf (cfg : OsCfg) (σ : Val) : ℕ → OsSt → ℕ → List OsLvK
  | _, _, 0 => []
  | lvl, s, n + 1 => osLvKOf cfg σ lvl s :: osLvsKOf cfg σ (lvl + 1) (osLevel cfg lvl (cfg.lv lvl) s).2 n

theorem os_sq_callS (cfg : OsCfg) (lvl : ℕ) (sg : OsSt) :
    (osLvSq cfg lvl sg).1.filterMap Main.Stmt.callS =
      [(some (.n (sg.k + 4)), (cfg.lv lvl).sqLoop, [.n (sg.k + 5), .n (sg.k + 6), .n (sg.k + 1), .n osQpos, .n osQbp],
        [])] := rfl

/-- **The levels' frames, level by level.** -/
theorem os_levels_calls (cfg : OsCfg) (σ : Val) : ∀ (n lvl : ℕ) (s : OsSt), lvl + n = cfg.levels.length →
    ((osLevels cfg lvl (cfg.levels.drop lvl) s).1.filterMap Main.Stmt.callS).map (Main.mkCall σ) =
      (osLvsKOf cfg σ lvl s n).flatMap OsLvK.calls
  | 0, lvl, s, h => by
    rw [List.drop_eq_nil_of_le (by omega)]; rfl
  | n + 1, lvl, s, h => by
    have hlt : lvl < cfg.levels.length := by omega
    have hdrop : cfg.levels.drop lvl = cfg.lv lvl :: cfg.levels.drop (lvl + 1) := by
      rw [List.drop_eq_getElem_cons hlt]
      simp [OsCfg.lv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    have hp1 : (osLevel cfg lvl (cfg.lv lvl) s).1 = (osLvF cfg lvl s).1 ++ (osLvM cfg lvl s).1 ++ (osLvG cfg lvl s).1 ++
        osLvStB cfg lvl (osLvG cfg lvl s).2 := congrArg Prod.fst (osLevel_parts cfg lvl s)
    rw [hdrop, osLevels_cons, List.filterMap_append, List.map_append,
      os_levels_calls cfg σ n (lvl + 1) _ (by omega), hp1]
    simp only [osLvsKOf, List.flatMap_cons, OsLvK.calls, osLvKOf, osLvStB_eq, List.filterMap_append, List.map_append,
      os_sq_callS, List.map_cons, List.append_assoc, List.cons_append, List.nil_append]

/-- **Each level's callees, placed**, from the levels' calls under the placed relations. -/
theorem os_lvsK_ok {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {cfg : OsCfg} {σ : Val} {Lk : Main.Layout}
    {W S : ℕ → ℕ → Main.Layout} {sqz rew : ℕ → E}
    (hne : ∀ l, l < cfg.levels.length → 1 + osGw (cfg.lv l).squeezes ≠ 0) :
    ∀ (n lvl : ℕ) (s : OsSt), lvl + n ≤ cfg.levels.length →
      OsLvsCallsOk (fun _ => osCA fs cert κ Lk) (fun l => osCB fs cert κ Lk (W l) (S l))
        (fun l => osCsq fs cert κ Lk (W l) (S l)) cfg σ sqz rew lvl s n →
      ∀ i (h : i < (osLvsKOf cfg σ lvl s n).length), OsLvKOk fs cert κ σ Lk (W (lvl + i)) (S (lvl + i))
        (osLvsKOf cfg σ lvl s n)[i]
  | 0, _, _, _, _, i, h => absurd h (by simp [osLvsKOf])
  | n + 1, lvl, s, hle, ⟨hA, hSq, hB, hsig, hrest⟩, i, h => by
    rcases i with _ | i
    · simp only [osLvsKOf, List.getElem_cons_zero, Nat.add_zero]
      have ht : (osLvKOf cfg σ lvl s).sq.taken = true := by
        simp only [osLvKOf, Main.mkCall, hsig.guard]
        exact decide_eq_true (hne lvl (by omega))
      refine ⟨fun c hc htk => hA c hc htk, ht, ?_, fun p c hc htk => hB c hc htk p⟩
      unfold OsCallsOk at hSq
      rw [os_sq_callS] at hSq
      exact hSq _ (List.mem_singleton.mpr rfl) ht
    · simp only [osLvsKOf, List.getElem_cons_succ]
      have := os_lvsK_ok hne n (lvl + 1) _ (by omega) hrest i (by simpa [osLvsKOf] using h)
      rw [show lvl + (i + 1) = lvl + 1 + i by omega]
      exact this

end
end LeanVM.Guest.B1
