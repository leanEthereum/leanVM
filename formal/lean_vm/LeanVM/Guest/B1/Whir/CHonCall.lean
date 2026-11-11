/-
  LeanVM.Guest.B1.Whir.CHonCall

  open_stacked's named callees at their honest arguments, from `OsH`.
-/

module

public import LeanVM.Guest.B1.Whir.CHonBuf
public import LeanVM.Guest.B1.Place.OsMean
public import LeanVM.Guest.B1.Whir.CTail
public import LeanVM.Guest.B1.Whir.CRoundsA

/-!
# The named callees, honestly

Under `OsH C rd c b own cur tabs xs`, a named callee holds in `C` on its meaning when its loads
are fixed (`OsFixedF`): `FixedAt p m`, the `m` words at `p` the same on every memory holding the
caller's words, from the cursor's words (`fixedAt_cur`) or a buffer's (`fixedAt_buf`).

Per kind, its meaning at the guest's honest arguments and returns: `om_pre` (`opening_message`),
`spf_pre`, `grind_pre`, `tail_pre`, `ffm_pre`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {c : OsCfg} {b : ℕ} {own : List (List E)} {cur tabs : E}
  {xs : List E}

/-! ## Reads -/

theorem readsAt_shift {p : E} {ys : List E} (h : ReadsAt rd p ys) (o m : ℕ) (hm : o + m ≤ ys.length) :
    ReadsAt rd (p * gen ^ o) ((ys.drop o).take m) := fun k hk ↦ by
  simp only [List.length_take, List.length_drop] at hk
  rw [loadHolds_mul_gen_pow, List.getElem_take, List.getElem_drop]
  exact h _ (by omega)

theorem readsAt_cons_iff {p x : E} {ys : List E} :
    ReadsAt rd p (x :: ys) ↔ LoadHolds rd p 0 x ∧ ReadsAt rd (p * gen ^ 1) ys := by
  constructor
  · intro h
    refine ⟨h 0 (by simp), fun k hk ↦ ?_⟩
    rw [loadHolds_mul_gen_pow]
    have := h (1 + k) (by simp; omega)
    simpa [show 1 + k = k + 1 by omega] using this
  · rintro ⟨h0, h1⟩ k hk
    rcases k with _ | k
    · exact h0
    · have := h1 k (by simpa using hk)
      rw [loadHolds_mul_gen_pow] at this
      simpa [show 1 + k = k + 1 by omega] using this

/-! ## Fixed loads -/

/-- **`m` words at `p` fixed** on every memory holding the caller's words. -/
def FixedAt (c : OsCfg) (b : ℕ) (own : List (List E)) (cur tabs : E) (xs : List E) (p : E) (m : ℕ) :
    Prop :=
  ∃ ws : List E, ws.length = m ∧ ∀ rd', ReadsAt rd' cur xs → WinTabs rd' tabs → OsMemF rd' c b own →
    ReadsAt rd' p ws

theorem fixedAt_cur {o m : ℕ} (h : o + m ≤ xs.length) : FixedAt c b own cur tabs xs (cur * gen ^ o) m :=
  ⟨(xs.drop o).take m, by simp only [List.length_take, List.length_drop]; omega, fun _ hr _ _ ↦ readsAt_shift hr o m h⟩

theorem fixedAt_buf {j o m : ℕ} (hj : j < (osSizesF c).length) (hne : j ≠ osIxQbp)
    (h : o + m ≤ (own.getD j []).length) : FixedAt c b own cur tabs xs (osPtrF c b j * gen ^ o) m :=
  ⟨((own.getD j []).drop o).take m, by simp only [List.length_take, List.length_drop]; omega, fun _ _ _ hm ↦ readsAt_shift (hm j hj hne) o m h⟩

theorem fixedAt_buf0 {j m : ℕ} (hj : j < (osSizesF c).length) (hne : j ≠ osIxQbp)
    (h : m ≤ (own.getD j []).length) : FixedAt c b own cur tabs xs (osPtrF c b j) m := by
  have := fixedAt_buf (own := own) (cur := cur) (tabs := tabs) (xs := xs) (b := b) (o := 0) (m := m) hj hne (by omega)
  simpa using this

theorem fixedAt_nil (p : E) : FixedAt c b own cur tabs xs p 0 := ⟨[], rfl, fun _ _ _ _ ↦ readsAt_nil _ _⟩

/-- **A named callee holds** on its meaning, its loads fixed. -/
theorem osH_named (hH : OsH C rd c b own cur tabs xs) {f : String} {K : OsKind}
    (hK : osKindOf f = some K) {a r : List E} (hp : K.Pre rd a r)
    (hx : ∀ q ∈ K.spec, FixedAt c b own cur tabs xs (a.getD q.1 0) q.2) : C f a r :=
  hH.2.2.2.1 f K hK a r hp hx

/-- **A special callee holds**. -/
theorem osH_special (hH : OsH C rd c b own cur tabs xs) {f : String} (hK : osKindOf f = none)
    (a r : List E) : C f a r :=
  hH.2.2.2.2 f a r hK

/-! ## The meanings at the honest arguments -/

theorem five_of {cap : List E} (h : cap.length = 5) :
    ∃ f0 f1 f2 f3 f4, cap = [f0, f1, f2, f3, f4] := by
  match cap, h with
  | [f0, f1, f2, f3, f4], _ => exact ⟨f0, f1, f2, f3, f4, rfl⟩

/-- `opening_message` without a nonce. -/
theorem om_pre {cap ms : List E} {p out : E} {n : ℕ} (hc : cap.length = 5) (hl : ms.length = n)
    (hr : ReadsAt rd p ms) (ho : ReadsAt rd out ms) :
    MeaningOpeningMessage n 0 rd (cap ++ [p, out]) (omRets cap ms none p n) := by
  obtain ⟨f0, f1, f2, f3, f4, rfl⟩ := five_of hc
  exact ⟨ms, hl, hr, ho, 0, fun h ↦ absurd h (by decide), by simp [omRets]⟩

/-- `opening_message` with a nonce. -/
theorem omN_pre {cap ms : List E} {p out nn : E} {n : ℕ} (hc : cap.length = 5) (hl : ms.length = n)
    (hr : ReadsAt rd p ms) (hn : LoadHolds rd p n nn) (ho : ReadsAt rd out ms) :
    MeaningOpeningMessage n 1 rd (cap ++ [p, out]) (omRets cap ms (some nn) p (n + 1)) := by
  obtain ⟨f0, f1, f2, f3, f4, rfl⟩ := five_of hc
  exact ⟨ms, hl, hr, ho, nn, fun _ ↦ hn, by simp [omRets]⟩

/-- `squeeze_point_from`. -/
theorem spf_pre {cap : List E} {first p : E} {n : ℕ} (hc : cap.length = 5)
    (hr : ReadsAt rd p (first :: ((⟨cap, []⟩ : Fs).squeezeN (n - 1)).1)) :
    MeaningSqueezePointFrom n rd (cap ++ [first, p]) ((⟨cap, []⟩ : Fs).squeezeN (n - 1)).2.cap := by
  obtain ⟨f0, f1, f2, f3, f4, rfl⟩ := five_of hc
  exact ⟨hr, rfl⟩

/-- `grind_check`. -/
theorem grind_pre {bits : ℕ} {w : E} (ht : WinTabs rd tabs) (hw : (w.limb 0).lane.toNat % 2 ^ bits = 0) :
    grindPre bits rd [w, tabs] [] :=
  ⟨rfl, w, tabs, rfl, ht, hw⟩

/-- `opening_tail_round`. -/
theorem tail_pre {cap : List E} {p cl t : E} {pr : E × E} (hc : cap.length = 5)
    (hr : ReadsAt rd p [pr.1, pr.2]) :
    MeaningOpeningTailRound rd (cap ++ [p, cl, t]) (tailRets cap p cl pr) := by
  obtain ⟨f0, f1, f2, f3, f4, rfl⟩ := five_of hc
  exact ⟨pr.1, pr.2, hr, rfl⟩

/-- `fold_final_msg`. -/
theorem ffm_pre {n : ℕ} {m ps : List E} {pm pp : E} (hm : m.length = 2 ^ n) (hp : ps.length = n)
    (hrm : ReadsAt rd pm m) (hrp : ReadsAt rd pp ps) :
    MeaningFoldFinalMsg n rd [pm, pp] [multilinearEval m ps] :=
  ⟨m, ps, hm, hp, hrm, hrp, rfl⟩

/-! ## The fold rounds -/

theorem roundRets_take_length (fs : List E) (cur cl : E) (w : List E) :
    ((roundRets fs cur cl w).take 5).length = 5 := by
  simp [roundRets, Fs.squeeze, capOf]

theorem mul_gen_pow_add (p : E) (a b : ℕ) : p * gen ^ a * gen ^ b = p * gen ^ (a + b) := by
  rw [mul_assoc, ← pow_add]

/-- **The fold rounds' calls**, from their memory and `OsH`'s named-callee clause. -/
theorem roundsC_of {cur0 : E} {xs0 : List E} {fch coefs : E}
    (hR : ∀ a r, MeaningOpeningRound rd a r → WinTabs rd (a.getD 7 0) →
      (∀ q ∈ OsKind.round.spec, FixedAt c b own cur0 tabs xs0 (a.getD q.1 0) q.2) →
      C "opening_round" a r) (ht : WinTabs rd tabs) :
    ∀ (n i : ℕ) (fs : List E) (cl cur : E) (ws : List E), fs.length = 5 → ws.length = 5 * n →
      ReadsAt rd cur ws → RoundsMem rd fch coefs n i fs cl ws →
      (∀ j < n, FixedAt c b own cur0 tabs xs0 (cur * gen ^ (5 * j)) 5 ∧
        FixedAt c b own cur0 tabs xs0 (fch * gen ^ (i + j)) 1 ∧
        FixedAt c b own cur0 tabs xs0 (coefs * gen ^ (2 * (i + j))) 2) →
      RoundsC C fch coefs tabs n i fs cl cur ws
  | 0, _, _, _, _, _, _, _, _, _, _ => trivial
  | n + 1, i, fs, cl, cur, ws, hfs, hwl, hrd, hm, hfx => by
    obtain ⟨hg, lg, la, lb, hm'⟩ := hm
    obtain ⟨f0, f1, f2, f3, f4, rfl⟩ := five_of hfs
    have hx7 : (ws.take 5).length = 5 := by simp [hwl]
    have hrd0 : ReadsAt rd cur (ws.take 5) := fun j hj ↦ by
      have := hrd j (by simp at hj; omega)
      simpa [List.getElem_take] using this
    have hrd1 : ReadsAt rd (cur * gen ^ 5) (ws.drop 5) := by
      have := readsAt_shift hrd 5 (ws.length - 5) (by omega)
      rwa [List.take_of_length_le (by simp)] at this
    refine ⟨hR _ _ (round_meaning hx7 hrd0 hg lg la lb) ht ?_, ?_⟩
    · obtain ⟨f1', f2', f3'⟩ := hfx 0 (by omega)
      simp only [Nat.mul_zero, pow_zero, mul_one, Nat.add_zero] at f1' f2' f3'
      intro q hq
      rw [show OsKind.round.spec = [(5, 5), (8, 1), (9, 2)] from rfl] at hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact f1'
      · exact f2'
      · exact f3'
    · refine roundsC_of hR ht n (i + 1) _ _ _ _ (roundRets_take_length _ _ _ _) (by simp [hwl]; omega) hrd1 hm'
        fun j hj ↦ ?_
      obtain ⟨a1, a2, a3⟩ := hfx (j + 1) (by omega)
      refine ⟨?_, ?_, ?_⟩
      · rw [mul_gen_pow_add, show 5 + 5 * j = 5 * (j + 1) by ring]; exact a1
      · rw [show i + 1 + j = i + (j + 1) by ring]; exact a2
      · rw [show 2 * (i + 1 + j) = 2 * (i + (j + 1)) by ring]; exact a3

end
end LeanVM.Guest.B1.Whir
