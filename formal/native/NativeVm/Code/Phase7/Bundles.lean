module

public import NativeVm.Code.Phase7.LevelKit

/-!
# The facts a level carries

Bundles of facts of the working area's words, each with the words it reads (`dep_*`): the level's
context (`LvB`: the ladder, the index, the levels left, the log-size, the batching scales), the
level's parameters (`Prm`, `Nxt`), WHIR's state and the rounds (`WRd`, reading only the glued claims
it has, `dep_whirP`), and single words (`na`, `ea`).
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model LeanVM.Parameters
open NativeVm.Transcript (wd Env wd_zero)

variable {p : Par}

/-- A number in an area word. -/
abbrev na (p : Par) (j n : Nat) (m : UInt64 → Option UInt64) : Prop := NatAt m (wd p.env.work j) n

/-- An element in two area words. -/
abbrev ea (p : Par) (j : Nat) (x : EW) (m : UInt64 → Option UInt64) : Prop :=
  EWAt m (wd p.env.work j) x

/-- WHIR's state reads its words up to its last glued claim. -/
theorem dep_whirP (sW : WhirStateW) (hg : sW.glued.size ≤ gluedCap) :
    Dep p.env (fun m ↦ WhirAt m (whirR.at p.env.work) sW)
      (fun k ↦ whirR.off ≤ k ∧ k < gslot sW.glued.size) := by
  intro m m' hm hw
  have hgc : sW.glued.size ≤ 10 := hg
  have sm : ∀ o n, whirR.off ≤ o → o + n ≤ gslot sW.glued.size → Same m m' (wd p.env.work o) n :=
    fun o n h1 h2 j hj ↦ by rw [wd_wd]; exact hm _ ⟨by omega, by omega⟩
  unfold WhirAt at hw ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw
  simp only [Region.at, wd_wd] at h1 h2 h4 h5 ⊢
  have s0 : Same m m' (wd p.env.work whirR.off) 2 := sm _ _ le_rfl (by simp only [gslot]; vomega)
  have s1 : Same m m' (wd p.env.work (whirR.off + 2)) (vecWords stackCap) :=
    sm _ _ (by omega) (by simp only [gslot]; vomega)
  have s2 : Same m m' (wd p.env.work (whirR.off + whirGluedOff)) 1 :=
    sm _ _ (by omega) (by simp only [gslot]; vomega)
  refine ⟨h1.congr s0, h2.congr s1, h3, h4.congr (s2.base (by omega) rfl),
    fun i hi ↦ (h5 i hi).congr (sm _ _ (by omega) ?_)⟩
  simp only [gslot]
  have : gluedWords * i + gluedWords ≤ gluedWords * sW.glued.size := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  omega

/-- The level's context. -/
def LvB (p : Par) (L : List Whir.Level) (logN k : Nat) (scales : Array EW)
    (m : UInt64 → Option UInt64) : Prop :=
  LevelsAt m (wd p.env.work levO) L ∧ na p cIdx k m ∧ na p cN (L.length - 1 - k) m ∧
    na p cLogN logN m ∧ EVec m (basisR.at p.env.work) stackClaimCap scales

theorem dep_LvB {L : List Whir.Level} (hl : L.length ≤ 6) (logN k : Nat) (scales : Array EW) :
    Dep p.env (LvB p L logN k scales) (fun j ↦ (levO ≤ j ∧ j < levO + 19) ∨ j = cIdx ∨ j = cN ∨
      j = cLogN ∨ (basisR.off ≤ j ∧ j < basisR.off + basisWords)) := by
  intro m m' hm ⟨h1, h2, h3, h4, h5⟩
  refine ⟨LevelsAt.congr (fun j hj ↦ by rw [wd_wd]; exact hm _ (.inl ⟨by omega, by
      rw [levelsWords_val] at hj; omega⟩)) hl h1,
    h2.congr (hm _ (.inr (.inl rfl))), h3.congr (hm _ (.inr (.inr (.inl rfl)))),
    h4.congr (hm _ (.inr (.inr (.inr (.inl rfl))))), h5.congr fun j hj ↦ ?_⟩
  rw [Region.at, wd_wd]
  exact hm _ (.inr (.inr (.inr (.inr ⟨by omega, by unfold basisWords; omega⟩))))

/-- A level's parameters. -/
def Prm (p : Par) (lv : Whir.Level) (m : UInt64 → Option UInt64) : Prop :=
  na p cFold lv.fold m ∧ na p cRate lv.logInvRate m ∧ na p cQ lv.queries m ∧ na p cJ lv.fold m

theorem dep_Prm (lv : Whir.Level) :
    Dep p.env (Prm p lv) (fun j ↦ j = cFold ∨ j = cRate ∨ j = cQ ∨ j = cJ) :=
  fun _ _ hm ⟨a, b, c, d⟩ ↦ ⟨a.congr (hm _ (.inl rfl)), b.congr (hm _ (.inr (.inl rfl))),
    c.congr (hm _ (.inr (.inr (.inl rfl)))), d.congr (hm _ (.inr (.inr (.inr rfl))))⟩

/-- The next level's fold and rate. -/
def Nxt (p : Par) (nx : Whir.Level) (m : UInt64 → Option UInt64) : Prop :=
  na p cNFold nx.fold m ∧ na p cNRate nx.logInvRate m

theorem dep_Nxt (nx : Whir.Level) : Dep p.env (Nxt p nx) (fun j ↦ j = cNFold ∨ j = cNRate) :=
  fun _ _ hm ⟨a, b⟩ ↦ ⟨a.congr (hm _ (.inl rfl)), b.congr (hm _ (.inr rfl))⟩

/-- WHIR's state and the level's rounds. -/
def WRd (p : Par) (sW : WhirStateW) (rs : Array FoldRoundW) (m : UInt64 → Option UInt64) : Prop :=
  WhirAt m (whirR.at p.env.work) sW ∧ RoundsAt m (roundsR.at p.env.work) rs

theorem dep_WRd (sW : WhirStateW) (hg : sW.glued.size ≤ gluedCap) (rs : Array FoldRoundW) :
    Dep p.env (WRd p sW rs) (fun k ↦ (whirR.off ≤ k ∧ k < gslot sW.glued.size) ∨
      (roundsR.off ≤ k ∧ k < roundsR.off + roundsWords)) :=
  (dep_whirP sW hg).and (dep_rounds rs)

theorem dep_na (j n : Nat) : Dep p.env (na p j n) (fun k ↦ k = j) :=
  fun _ _ hm h ↦ h.congr (hm _ rfl)

theorem dep_ea (j : Nat) (x : EW) : Dep p.env (ea p j x) (fun k ↦ k = j ∨ k = j + 1) :=
  fun _ _ hm h ↦ h.congr fun i hi ↦ by
    rw [wd_wd]; exact hm _ (by omega)

theorem dep_ewarr (j : Nat) (xs : Array EW) :
    Dep p.env (fun m ↦ EWArr m (wd p.env.work j) xs) (fun k ↦ j ≤ k ∧ k < j + 2 * xs.size) :=
  fun _ _ hm h ↦ h.congr (n := 2 * xs.size) (fun i hi ↦ by rw [wd_wd]; exact hm _ ⟨by omega, by omega⟩)
    le_rfl

theorem dep_wvec (j : Nat) (xs : Array UInt64) :
    Dep p.env (fun m ↦ WVec m (wd p.env.work j) queryCap xs)
      (fun k ↦ j ≤ k ∧ k < j + wvecWords queryCap) :=
  fun _ _ hm h ↦ h.congr fun i hi ↦ by rw [wd_wd]; exact hm _ ⟨by omega, by omega⟩

theorem dep_evec (j cap : Nat) (xs : Array EW) :
    Dep p.env (fun m ↦ EVec m (wd p.env.work j) cap xs) (fun k ↦ j ≤ k ∧ k < j + vecWords cap) :=
  fun _ _ hm h ↦ h.congr fun i hi ↦ by rw [wd_wd]; exact hm _ ⟨by omega, by omega⟩

theorem dep_const (P : Prop) : Dep p.env (fun _ ↦ P) (fun _ ↦ False) := fun _ _ _ h ↦ h

theorem dep_table (mu : Nat) (hmu : mu ≤ 30) :
    Dep p.env (fun m ↦ TableAt m (wd p.env.work tabO) (subspaceTable mu))
      (fun k ↦ tabO ≤ k ∧ k < tabO + 62) := by
  intro m m' hm h i hi
  have hs : (subspaceTable mu).size = mu + 1 := subspaceTable_size mu
  obtain ⟨h1, h2⟩ := h i hi
  rw [wd_wd] at h1 h2 ⊢
  rw [wd_wd, hm _ ⟨by omega, by omega⟩, hm _ ⟨by omega, by omega⟩]
  exact ⟨h1, h2⟩

/-- The opened rows with their width (`queryC`'s result). -/
def RowsW (p : Par) (words : Array (Array UInt64)) (n : Nat) (m : UInt64 → Option UInt64) : Prop :=
  ∃ width, RowsAt m (wd p.env.work rowsR.off) width words ∧ words.size = n ∧ width ≤ 64 ∧
    na p (tmpO + 24) width m

theorem dep_RowsW (words : Array (Array UInt64)) (n : Nat) :
    Dep p.env (RowsW p words n) (fun k ↦ (rowsR.off ≤ k ∧ k < rowsR.off + rowsWords) ∨ k = tmpO + 24) := by
  intro m m' hm ⟨w, ⟨hcap, hr⟩, hsz, hw, hwd⟩
  refine ⟨w, ⟨hcap, fun i hi ↦ ⟨(hr i hi).1, fun j hj ↦ ?_⟩⟩, hsz, hw, hwd.congr (hm _ (.inr rfl))⟩
  have hj' : j < w := by rw [← (hr i hi).1]; exact hj
  have : w * i + w ≤ words.size * w := by
    rw [Nat.mul_comm w i, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
  have hrw : rowsWords = 16384 := by decide
  have h1 := (hr i hi).2 j hj
  rw [wd_wd, wd_wd] at h1 ⊢
  rw [hm _ (.inl ⟨by omega, by rw [hrw] at hcap ⊢; omega⟩)]
  exact h1

end NativeVm.Code.P7
