/-
  LeanVM.Guest.B1.Whir.CHonCall

  open_stacked's named callees at their honest arguments, from `OsHA`.
-/

module

public import LeanVM.Guest.B1.Whir.CHonBuf
public import LeanVM.Guest.B1.Place.OsProtoSpec
public import LeanVM.Guest.B1.Place.OsMean
public import LeanVM.Guest.B1.Whir.CTail
public import LeanVM.Guest.B1.Whir.CRoundsA

/-!
# The named callees, honestly

Under `OsHA C rd c b own cur tabs xs`, a named callee holds in `C` on its meaning when its loads
are fixed (`OsFixedA`): `FixedAt p m`, the `m` words at `p` the same on every memory holding the
caller's words, from the cursor's words (`fixedAt_cur`) or a buffer's (`fixedAt_buf`).

Per kind, its meaning at the guest's honest arguments and returns: `om_pre` (`opening_message`),
`spf_pre`, `tail_pre`, `ffm_pre`.
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

/-! ## Fixed loads -/

/-- **`m` words at `p` fixed** on every memory holding the caller's words. -/
def FixedAt (c : OsCfg) (b : ℕ) (own : List (List E)) (cur tabs : E) (xs : List E) (p : E) (m : ℕ) :
    Prop :=
  ∃ ws : List E, ws.length = m ∧ ∀ rd', ReadsAt rd' cur xs → WinTabs rd' tabs → OsMemA rd' c b own →
    ReadsAt rd' p ws

theorem fixedAt_cur {o m : ℕ} (h : o + m ≤ xs.length) : FixedAt c b own cur tabs xs (cur * gen ^ o) m :=
  ⟨(xs.drop o).take m, by simp only [List.length_take, List.length_drop]; omega, fun _ hr _ _ ↦ readsAt_shift hr o m h⟩

theorem fixedAt_buf {j o m : ℕ} (hj : j < (osSizesL c).length) (hne : j ≠ osIxQbpA)
    (h : o + m ≤ (own.getD j []).length) : FixedAt c b own cur tabs xs (osPtrA c b j * gen ^ o) m :=
  ⟨((own.getD j []).drop o).take m, by simp only [List.length_take, List.length_drop]; omega, fun _ _ _ hm ↦ readsAt_shift (hm j hj hne) o m h⟩

theorem fixedAt_buf0 {j m : ℕ} (hj : j < (osSizesL c).length) (hne : j ≠ osIxQbpA)
    (h : m ≤ (own.getD j []).length) : FixedAt c b own cur tabs xs (osPtrA c b j) m := by
  have := fixedAt_buf (own := own) (cur := cur) (tabs := tabs) (xs := xs) (b := b) (o := 0) (m := m) hj hne (by omega)
  simpa using this

/-- **A named callee holds** on its meaning, its loads fixed. -/
theorem osH_named (hH : OsHA C rd c b own cur tabs xs) {f : String} {K : OsKind}
    (hK : osKindOf f = some K) {a r : List E} (hp : K.Pre rd a r)
    (hx : ∀ q ∈ K.spec, FixedAt c b own cur tabs xs (a.getD q.1 0) q.2) : C f a r :=
  hH.2.2.2.1 f K hK a r hp hx

/-- **A special callee holds**. -/
theorem osH_special (hH : OsHA C rd c b own cur tabs xs) {f : String} (hK : osKindOf f = none)
    (a r : List E) : C f a r :=
  hH.2.2.2.2 f a r hK

/-- **`is_zero` holds on every word**, a named callee of no loads. -/
theorem osHA_iz : IsZeroC (fun C rd ↦ OsHA C rd c b own cur tabs xs) := fun _ _ hH w ↦
  osH_named hH osKindOf_isZero (show MeaningIsZero [w] [zeroOf w] from rfl) fun q hq ↦ by simp [OsKind.spec] at hq

/-- **The memory facts of `OsHA`**, the call relation trivial. -/
abbrev OsM (c : OsCfg) (b : ℕ) (own : List (List E)) (cur tabs : E) (xs : List E) : Reader → Prop :=
  fun rd ↦ OsHA (fun _ _ _ ↦ True) rd c b own cur tabs xs

/-- `OsHA` on `HM` of its memory facts and a relation within `OsHA`. -/
theorem osHA_of_hm {H : CallRel → Reader → Prop} (hH : ∀ C rd, H C rd → OsHA C rd c b own cur tabs xs)
    (h : HM (OsM c b own cur tabs xs) H C rd) : OsHA C rd c b own cur tabs xs :=
  h.elim (hH C rd) fun h ↦ by rw [h.2.1]; exact h.1

theorem osHA_izHM {H : CallRel → Reader → Prop} (hH : ∀ C rd, H C rd → OsHA C rd c b own cur tabs xs) :
    IsZeroC (HM (OsM c b own cur tabs xs) H) := fun C rd h w ↦ osHA_iz C rd (osHA_of_hm hH h) w

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

end
end LeanVM.Guest.B1.Whir
