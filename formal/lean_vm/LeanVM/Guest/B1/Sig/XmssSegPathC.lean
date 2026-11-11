/-
  LeanVM.Guest.B1.Sig.XmssSegPathC

  The path of the leanXMSS check in `__loop2` (`lx_window`, `lx_top_window`, `lx_levels`,
  `lean_ethereum.py:3602-3642, 3705-3714`), complete a window at a time: the dispatch by the
  honest window `lxWin L w`, each level's sibling hinted, the arm's pin by `lx_his_honest`.
-/

module

public import LeanVM.Guest.B1.Sig.XmssSegPath
public import LeanVM.Guest.B1.Sig.XmssSegStepC
public import LeanVM.Guest.B1.Sig.XmssBound
public import LeanVM.Guest.B1.Sig.CwComplete
public import LeanVM.Guest.B1.Sig.XmssSegWinSpec

/-!
# A window of the path, complete

* `CompletesO`: completeness changing a range and, besides, the one-cell run at `o` (an arm
  `k ≠ 0` of a window writes its output where arm `0` numbered it); `Completes.appendO`,
  `CompletesO.append`, `CompletesO.toC`, `k64_completeO`;
* `LxEnv`: the values below `103` a window reads (the padding run, `P`, the shifts `his[v]` of the
  index `L`, the powers `g^s`);
* `lxLevelT_complete`, `lxLevelsT_complete`, `lxArmT_complete`: a level, the eight levels and an
  arm of window `w` by the honest arm `lxWin L w`, each level's sibling hinted;
* `lxWindowT_complete`: the window completes, the siblings the hinted
  ones; `lxWindowT_complete_fold`: its output is the fold of its eight levels over the index;
* `lxWindowT_numBelow`: the window's values lie below its end;
* `lxWindows_complete`: a layer's two windows complete, their output the layer's path fold
  `xFold` over the addresses `lxLayerA` and bits `lxLayerBit` of the index.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## Completeness writing a run elsewhere -/

/-- `σ'` is `σ` outside `lo ..< hi` and the one-cell run at `o`. -/
def ExtO (lo hi o : Nat) (σ σ' : Val) : Prop :=
  ∀ v, (∀ k, lo ≤ k → k < hi → v ≠ .n k) → ¬ InR o 1 v → σ' v = σ v

/-- **Completeness changing `lo ..< hi` and the run at `o`.** -/
def CompletesO (C : CallRel) (rd : Reader) (lo hi o : Nat) (ss : List Stmt) (σ : Val)
    (Post : Val → Prop) : Prop :=
  ∃ σ', ExtO lo hi o σ σ' ∧ Post σ' ∧
    ∀ (next : Prop) (kret : List E → Prop), next → Stmt.HoldsList C rd σ' ss next kret

theorem ExtO.apply {lo hi o : Nat} {σ σ' : Val} (h : ExtO lo hi o σ σ') {j : Nat}
    (hj : j < lo ∨ hi ≤ j) (ho : j < o ∨ o + 1 ≤ j) : σ' (.n j) = σ (.n j) :=
  h _ (fun k h1 h2 e => by simp only [V.mk.injEq, true_and] at e; omega)
    (by rintro ⟨i, hi, e⟩; simp only [V.mk.injEq, true_and] at e; omega)

theorem Completes.toO {lo hi : Nat} (o : Nat) {ss : List Stmt} {σ : Val} {P : Val → Prop}
    (h : Completes C rd lo hi ss σ P) : CompletesO C rd lo hi o ss σ P :=
  let ⟨σ', he, hp, hh⟩ := h; ⟨σ', fun v hv _ => he v hv, hp, hh⟩

/-- A block writing only the run at `o`. -/
theorem Completes.toO_run {lo hi o : Nat} {ss : List Stmt} {σ : Val} {P : Val → Prop}
    (h : Completes C rd o (o + 1) ss σ P) : CompletesO C rd lo hi o ss σ P :=
  let ⟨σ', he, hp, hh⟩ := h
  ⟨σ', fun v _ hr => he v (fun k h1 h2 e => hr ⟨k - o, by omega, by rw [e]; congr 1; omega⟩), hp, hh⟩

theorem CompletesO.toC {lo hi o lo' hi' : Nat} {ss : List Stmt} {σ : Val} {P : Val → Prop}
    (h : CompletesO C rd lo hi o ss σ P) (hlo : lo' ≤ lo) (hlo' : lo' ≤ o) (hhi : hi ≤ hi')
    (hhi' : o + 1 ≤ hi') : Completes C rd lo' hi' ss σ P :=
  let ⟨σ', he, hp, hh⟩ := h
  ⟨σ', fun v hv => he v (fun k h1 h2 => hv k (by omega) (by omega))
    (by rintro ⟨i, hi, rfl⟩; exact hv (o + i) (by omega) (by omega) rfl), hp, hh⟩

theorem CompletesO.mono {lo hi o lo' hi' : Nat} {ss : List Stmt} {σ : Val} {P Q : Val → Prop}
    (h : CompletesO C rd lo hi o ss σ P) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') (hPQ : ∀ σ', P σ' → Q σ') :
    CompletesO C rd lo' hi' o ss σ Q :=
  let ⟨σ', he, hp, hh⟩ := h
  ⟨σ', fun v hv hr => he v (fun k h1 h2 => hv k (by omega) (by omega)) hr, hPQ σ' hp, hh⟩

theorem CompletesO.reload {lo hi o : Nat} {ss : List Stmt} {σ σr : Val} {P : Val → Prop}
    (he : Ext lo hi σ σr) (h : CompletesO C rd lo hi o ss σr P) : CompletesO C rd lo hi o ss σ P :=
  let ⟨σ', he', hp, hh⟩ := h
  ⟨σ', fun v hv hr => (he' v hv hr).trans (he v hv), hp, hh⟩

/-- **A block, then one writing the run at `o` besides its range.** -/
theorem Completes.appendO {lo m hi o : Nat} {xs ys : List Stmt} {σ : Val} {P Q : Val → Prop}
    (hlo : lo ≤ m) (hhi : m ≤ hi) (hxs : ∀ v ∈ Stmt.valsList xs, NBv m v ∧ ¬ InR o 1 v)
    (h1 : Completes C rd lo m xs σ P) (h2 : ∀ σ', Ext lo m σ σ' → P σ' → CompletesO C rd m hi o ys σ' Q) :
    CompletesO C rd lo hi o (xs ++ ys) σ Q := by
  obtain ⟨σ1, he1, hp1, hh1⟩ := h1
  obtain ⟨σ2, he2, hq2, hh2⟩ := h2 σ1 he1 hp1
  refine ⟨σ2, fun v hv hr => ?_, hq2, fun next kret hn => ?_⟩
  · rw [he2 v (fun k h1 h2 => hv k (by omega) h2) hr, he1 v (fun k h1 h2 => hv k h1 (by omega))]
  · rw [holdsList_append]
    refine (holdsList_congr xs (fun v hv => ?_) _ _).mp (hh1 _ kret (hh2 next kret hn))
    obtain ⟨⟨j, hj, rfl⟩, hr⟩ := hxs v hv
    exact (he2 _ (fun k h1 h2 e => by simp only [V.mk.injEq, true_and] at e; omega) hr).symm

theorem CompletesO.keep {lo hi o : Nat} {ss : List Stmt} {σ : Val} {P : Val → Prop}
    (h : CompletesO C rd lo hi o ss σ P) : CompletesO C rd lo hi o ss σ (fun σ' => P σ' ∧ ExtO lo hi o σ σ') :=
  let ⟨σ', he, hp, hh⟩ := h; ⟨σ', he, ⟨hp, he⟩, hh⟩

/-- **A block writing the run at `o`, then one on the next range.** -/
theorem CompletesO.append {lo m hi o : Nat} {xs ys : List Stmt} {σ : Val} {P Q : Val → Prop}
    (hlo : lo ≤ m) (hhi : m ≤ hi) (hxs : NumBelow m (Stmt.valsList xs))
    (h1 : CompletesO C rd lo m o xs σ P) (h2 : ∀ σ', ExtO lo m o σ σ' → P σ' → Completes C rd m hi ys σ' Q) :
    CompletesO C rd lo hi o (xs ++ ys) σ Q := by
  obtain ⟨σ1, he1, hp1, hh1⟩ := h1
  obtain ⟨σ2, he2, hq2, hh2⟩ := h2 σ1 he1 hp1
  refine ⟨σ2, fun v hv hr => ?_, hq2, fun next kret hn => ?_⟩
  · rw [he2 v (fun k h1 h2 => hv k (by omega) h2), he1 v (fun k h1 h2 => hv k h1 (by omega)) hr]
  · rw [holdsList_append]
    exact (holdsList_frame hxs he2.agree _ _).mp (hh1 _ kret (hh2 next kret hn))

/-! ## A `KECCAK` writing its run anywhere -/

/-- **A 64-byte `keccak` completes**, its constant at `c` and its run at `o` off its inputs. -/
theorem k64_completeO {pad : Nat} {m0 m1 m2 m3 : V} {c o : Nat} (σ : Val) (hpo : pad + 5 ≤ o) (hco : c + 1 ≤ o ∨ o + 1 ≤ c)
    (hm : ∀ v ∈ [m0, m1, m2, m3], NBv c v ∧ ¬ InR o 1 v) :
    CompletesO C rd c (c + 1) o (k64 pad m0 m1 m2 m3 c o) σ (fun _ => True) := by
  rw [k64_vals_eq]
  refine Completes.appendO (m := c + 1) (by omega) le_rfl (fun v hv => ?_) (cst_complete σ c _) (fun σ1 he1 hp1 => ?_)
  · simp only [cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
      List.mem_singleton] at hv
    subst hv
    exact ⟨⟨c, by omega, rfl⟩, by rintro ⟨j, hj, e⟩; simp only [V.mk.injEq, true_and] at e; omega⟩
  have hag : AgreeBelow c σ σ1 := he1.agree
  have hin : ∀ v ∈ [m0, m1, m2, m3, .n pad, .n (pad + 1), .n (pad + 2), .n (pad + 3), .n c, .n (pad + 1),
      .n (pad + 2), .n (pad + 3), .n (pad + 4)], ¬ InR o 1 v := by
    intro v hv
    rcases (k64_ins pad m0 m1 m2 m3 c v).mp hv with h | rfl | ⟨k, hk, rfl⟩
    · exact (hm v h).2
    · rintro ⟨j, hj, e⟩; simp only [V.mk.injEq, true_and] at e; omega
    · rintro ⟨j, hj, e⟩; simp only [V.mk.injEq, true_and] at e; omega
  exact (kecS_complete_at (C := C) (rd := rd) σ1 o (.inl rfl) rfl hin false false).toO_run.mono le_rfl
    le_rfl (fun _ _ => trivial)

/-! ## A level, generically -/

/-- **A level completes**: sequential values `b ..< s`, the hinted sibling at `s` (loaded), the
sequential values `s + 1 ..< c`, the `keccak` at `c` writing the run at `o`. -/
theorem lvl_completeO {xs ys : List Stmt} {nm : String} {b s c o pad : Nat} {m0 m1 m2 m3 : V}
    (σ : Val) (hx : SeqOK b xs s) (hy : SeqOK (s + 1) ys c)
    (hco : c + 1 ≤ o ∨ o + 1 ≤ b) (hpo : pad + 5 ≤ o)
    (hxo : ∀ v ∈ Stmt.valsList xs ++ Stmt.valsList ys, ¬ InR o 1 v)
    (hm : ∀ σ1, Ext b c σ σ1 → σ1 (.n s) = σ (.n s) →
      AtomsHold rd σ1 (xs ++ hintW nm [.n s] :: ys) →
      ∀ v ∈ [m0, m1, m2, m3], NBv c v ∧ ¬ InR o 1 v) :
    CompletesO C rd b (c + 1) o (xs ++ hintW nm [.n s] :: ys ++ k64 pad m0 m1 m2 m3 c o) σ
      (fun σ' => σ' (.n s) = σ (.n s)) := by
  have hsb := hx.le
  have hsc := hy.le
  have hatoms : atomsOnly (xs ++ hintW nm [.n s] :: ys) = true := by
    rw [atomsOnly_append, hx.atoms]
    exact hy.atoms
  have hpre : Completes C rd b c (xs ++ hintW nm [.n s] :: ys) σ (fun σ1 => σ1 (.n s) = σ (.n s)) := by
    refine Completes.seq hx (by omega) (fun σa hea _ => ?_)
    obtain ⟨σ1, he1, -, hh1⟩ := seq_completes (C := C) (rd := rd) hy σa
    refine (Completes.hint (lo := s + 1) (hi := c) (.cons ⟨s, by omega, rfl⟩ (.nil _)) (by omega)
      ⟨σ1, he1, ?_, hh1⟩).mono (by omega) le_rfl (fun _ h => h)
    show σ1 (.n s) = σ (.n s)
    rw [he1.apply (Or.inl (by omega)), hea.apply (Or.inr le_rfl)]
  have hvals : ∀ v ∈ Stmt.valsList (xs ++ hintW nm [.n s] :: ys), NBv c v ∧ ¬ InR o 1 v := by
    intro v hv
    rw [show xs ++ hintW nm [.n s] :: ys = xs ++ [hintW nm [.n s]] ++ ys by simp, valsList_append,
      valsList_append, valsList_hint] at hv
    rcases List.mem_append.mp hv with hv | hv
    · rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨j, hj, rfl⟩ := hx.numBelow _ hv
        exact ⟨⟨j, by omega, rfl⟩, hxo _ (List.mem_append_left _ hv)⟩
      · simp only [List.mem_singleton] at hv
        subst hv
        refine ⟨⟨s, by omega, rfl⟩, ?_⟩
        rintro ⟨j, hj, e⟩; simp only [V.mk.injEq, true_and] at e; omega
    · obtain ⟨j, hj, rfl⟩ := hy.numBelow _ hv
      exact ⟨⟨j, by omega, rfl⟩, hxo _ (List.mem_append_right _ hv)⟩
  rw [List.append_assoc, List.cons_append, ← List.cons_append, ← List.append_assoc]
  refine Completes.appendO (by omega) (by omega) hvals hpre.withHolds (fun σ1 he1 ⟨hs1, hh1⟩ => ?_)
  have hm1 := hm σ1 he1 hs1 (atomsHold_of_holdsList hatoms hh1)
  refine (k64_completeO (C := C) (rd := rd) σ1 hpo
    (by omega) hm1).keep.mono le_rfl le_rfl (fun σ' ⟨_, he⟩ => ?_)
  rw [he.apply (Or.inl (by omega)) (by omega), hs1]

/-! ## The values a window reads -/

/-- The values below `103` a window of the index `L` reads: the padding run, the shifts
`his[v] = L >>> 8v` and the powers `g^s`. -/
def LxEnv (L : Nat) (σ : Val) : Prop :=
  PadOK σ sLxPad ∧ (∀ v < 4, σ (sHis v) = eOfNat (L >>> (8 * v))) ∧ ∀ s < 13, σ (sPower s) = gen ^ s

theorem LxEnv.congr {L : Nat} {σ σ' : Val} (h : LxEnv L σ) (hσ : ∀ j < 103, σ' (.n j) = σ (.n j)) :
    LxEnv L σ' := by
  obtain ⟨h1, h3, h4⟩ := h
  refine ⟨h1.congr (b := 103) (by simp [sLxPad]) (fun j hj => (hσ j hj).symm), fun v hv => ?_,
    fun s hs => ?_⟩
  · rw [show sHis v = .n (67 + v) from rfl, hσ _ (by omega)]; exact h3 v hv
  · rw [show sPower s = .n (75 + s) from rfl, hσ _ (by omega)]; exact h4 s hs

theorem notInR_of {o j : Nat} (h : j < o ∨ o + 1 ≤ j) : ¬ InR o 1 (.n j) := by
  rintro ⟨i, hi, e⟩; simp only [V.mk.injEq, true_and] at e; omega

theorem ord_cases {k r : Nat} (x y : V) :
    ((if k / 2 ^ r % 2 = 0 then (x, y) else (y, x)).1 = x ∧ (if k / 2 ^ r % 2 = 0 then (x, y) else (y, x)).2 = y) ∨
    ((if k / 2 ^ r % 2 = 0 then (x, y) else (y, x)).1 = y ∧ (if k / 2 ^ r % 2 = 0 then (x, y) else (y, x)).2 = x) := by
  split
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- A level's inputs: `P`, the address at `a`, the node and the sibling at `s` in either order. -/
theorem lvl_inputs {cur m2 m3 : V} {s a c o : Nat}
    (hcur : NBv c cur) (hcurO : ¬ InR o 1 cur) (hs : s < c) (hsO : s < o ∨ o + 1 ≤ s)
    (ha : a < c) (haO : a < o ∨ o + 1 ≤ a) (h66 : 66 < c) (ho : 103 ≤ o)
    (h23 : (m2 = cur ∧ m3 = .n s) ∨ (m2 = .n s ∧ m3 = cur)) :
    ∀ v ∈ [sLxPP, .n a, m2, m3], NBv c v ∧ ¬ InR o 1 v := by
  have hcv : NBv c cur ∧ ¬ InR o 1 cur := ⟨hcur, hcurO⟩
  have hsv : NBv c (.n s) ∧ ¬ InR o 1 (.n s) := ⟨⟨s, hs, rfl⟩, notInR_of hsO⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro v (rfl | rfl | rfl | rfl)
  · exact ⟨⟨66, h66, rfl⟩, notInR_of (by omega)⟩
  · exact ⟨⟨a, ha, rfl⟩, notInR_of haO⟩
  · rcases h23 with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [hcv, hsv]
  · rcases h23 with ⟨-, rfl⟩ | ⟨-, rfl⟩
    exacts [hsv, hcv]

/-! ## A level -/

/-- Where level `r` of window `w` from base `b` writes its node. -/
def lxLvlO (w r : Nat) (outO : Option Nat) (b : Nat) : Nat :=
  if w + 1 = 4 then (if r + 1 = 8 then outO.getD (b + 3) else b + 3)
  else if r + 1 = 8 then outO.getD (b + 4) else b + 5

theorem lxLevelT_out (w k r : Nat) (cur : V) (outO : Option Nat) (b : Nat) :
    (lxLevelT w k r cur outO b).2.2 = .n (lxLvlO w r outO b) := by
  unfold lxLevelT lxLvlO
  by_cases hw : w + 1 = 4 <;> by_cases hr : r + 1 = 8 <;> simp [hw, hr]

theorem getD_cases {outO : Option Nat} {b d : Nat} {cur : V}
    (hO : ∀ o, outO = some o → 103 ≤ o ∧ o + 1 ≤ b ∧ ¬ InR o 1 cur) :
    outO.getD d = d ∨ (103 ≤ outO.getD d ∧ outO.getD d + 1 ≤ b ∧ ¬ InR (outO.getD d) 1 cur) := by
  cases outO with
  | none => exact Or.inl rfl
  | some o => exact Or.inr (hO o rfl)

/-- **A level of a window completes** by the honest arm, its sibling `sib` hinted. -/
theorem lxLevelT_complete {L : Nat} {w r : Nat} (hw : w < 4) (hr : r < 8) {cur : V}
    {outO : Option Nat} {b : Nat} (σ : Val) (hb : 103 ≤ b) (hcur : NBv b cur)
    (hO : ∀ o, outO = some o → 103 ≤ o ∧ o + 1 ≤ b ∧ ¬ InR o 1 cur) {sib : E} :
    CompletesO C rd b (lxLevelT w (lxWin L w) r cur outO b).2.1 (lxLvlO w r outO b)
      (lxLevelT w (lxWin L w) r cur outO b).1 σ (fun σ' => σ' (.n (lxSibCell w r b)) = sib) := by
  obtain ⟨jc, hjc, rfl⟩ := hcur
  unfold lxLevelT lxLvlO lxSibCell
  by_cases hw3 : w + 1 = 4
  · simp only [hw3, ↓reduceIte]
    generalize hOd : (if r + 1 = 8 then outO.getD (b + 3) else b + 3) = O
    have hOc : O = b + 3 ∨ (103 ≤ O ∧ O + 1 ≤ b ∧ ¬ InR O 1 (.n jc)) := by
      rw [← hOd]; split
      · exact getD_cases hO
      · exact Or.inl rfl
    have hcO : ¬ InR O 1 (.n jc) := by
      rcases hOc with h | h
      · exact notInR_of (by omega)
      · exact h.2.2
    refine CompletesO.reload (σr := Function.update σ (.n b) sib) (fun v hv => Function.update_of_ne
      (hv b le_rfl (by split <;> omega)) _ _) ?_
    have hσr : ∀ j, j ≠ b → Function.update σ (.n b) sib (.n j) = σ (.n j) := fun j hj =>
      Function.update_of_ne (by simp only [ne_eq, V.mk.injEq, true_and]; exact hj) _ _
    refine (lvl_completeO (xs := []) (ys := [cst (b + 1) (word (lxNodeConst w r + lxWin L w / 2 ^ (r + 1)) 0)])
      (nm := "lx_path") (s := b) (c := b + 2) (o := O) _ rfl ⟨rfl, rfl⟩
      (by omega) (by simp only [sLxPad]; rcases hOc with h | h <;> omega) ?_ ?_).mono le_rfl (by split <;> omega)
      (fun σ' h1 => by rw [h1, Function.update_self])
    · intro v hv
      simp [cst, Stmt.vals, Atom.vals] at hv
      subst hv
      exact notInR_of (by rcases hOc with h | h <;> omega)
    · intro _ _ _ _
      exact lvl_inputs ⟨jc, by omega, rfl⟩ hcO (by omega)
        (by rcases hOc with h | h <;> omega) (by omega)
        (by rcases hOc with h | h <;> omega) (by omega)
        (by rcases hOc with h | h <;> omega) (ord_cases _ _)
  · simp only [hw3, ↓reduceIte]
    have hσr : ∀ (s j : Nat), j ≠ s → Function.update σ (.n s) sib (.n j) = σ (.n j) := fun s j hj =>
      Function.update_of_ne (by simp only [ne_eq, V.mk.injEq, true_and]; exact hj) _ _
    have hhis : NBv b (sHis (w + 1)) := ⟨67 + (w + 1), by omega, rfl⟩
    by_cases hr7 : r + 1 = 8
    · obtain rfl : r = 7 := by omega
      simp only [show 7 + 1 = 8 from rfl, ↓reduceIte]
      generalize hOd : outO.getD (b + 4) = O
      have hOc : O = b + 4 ∨ (103 ≤ O ∧ O + 1 ≤ b ∧ ¬ InR O 1 (.n jc)) := by
        rw [← hOd]; exact getD_cases hO
      have hcO : ¬ InR O 1 (.n jc) := by
        rcases hOc with h | h
        · exact notInR_of (by omega)
        · exact h.2.2
      refine CompletesO.reload (σr := Function.update σ (.n (b + 2)) sib) (fun v hv => Function.update_of_ne
        (hv (b + 2) (by omega) (by cases outO <;> simp)) _ _) ?_
      refine (lvl_completeO (xs := [cst b (word (lxNodeConst w 7 + lxWin L w / 2 ^ 8) 0),
          addS (.n (b + 1)) (sHis (w + 1)) (.n b)]) (ys := [])
        (nm := "lx_path") (s := b + 2) (c := b + 3) (o := O) _ ⟨rfl, ⟨rfl, hhis.mono' (by omega),
          ⟨b, by omega, rfl⟩⟩, rfl⟩ rfl
        (by omega) (by simp only [sLxPad]; rcases hOc with h | h <;> omega) ?_ ?_).mono le_rfl
        (by cases outO <;> simp) (fun σ' h1 => by rw [h1, Function.update_self])
      · intro v hv
        simp [cst, addS, Stmt.vals, Atom.vals] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact notInR_of (by rcases hOc with h | h <;> omega)
      · intro _ _ _ _
        exact lvl_inputs ⟨jc, by omega, rfl⟩ hcO (by omega)
          (by rcases hOc with h | h <;> omega) (by omega)
          (by rcases hOc with h | h <;> omega)
          (by omega) (by rcases hOc with h | h <;> omega) (ord_cases _ _)
    · simp only [hr7, ↓reduceIte]
      have hpw : NBv b (sPower (7 - r)) := ⟨75 + (7 - r), by omega, rfl⟩
      refine CompletesO.reload (σr := Function.update σ (.n (b + 3)) sib) (fun v hv => Function.update_of_ne
        (hv (b + 3) (by omega) (by omega)) _ _) ?_
      refine (lvl_completeO (xs := [mulS (.n b) (sHis (w + 1)) (sPower (7 - r)),
          cst (b + 1) (word (lxNodeConst w r + lxWin L w / 2 ^ (r + 1)) 0),
          addS (.n (b + 2)) (.n b) (.n (b + 1))]) (ys := [])
        (nm := "lx_path") (s := b + 3) (c := b + 4) (o := b + 5) _
        ⟨⟨rfl, hhis, hpw⟩, rfl, ⟨rfl, ⟨b, by omega, rfl⟩, ⟨b + 1, by omega, rfl⟩⟩, rfl⟩ rfl
        (by omega) (by simp only [sLxPad]; omega) ?_ ?_).mono le_rfl
        (by omega) (fun σ' h1 => by rw [h1, Function.update_self])
      · intro v hv
        simp [cst, addS, mulS, Stmt.vals, Atom.vals] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact notInR_of (by omega)
      · intro _ _ _ _
        exact lvl_inputs ⟨jc, by omega, rfl⟩ (notInR_of (by omega)) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (ord_cases _ _)


/-! ## A level's values -/

theorem k64_vals_all {pad : Nat} {m0 m1 m2 m3 : V} {c o : Nat} {P : V → Prop}
    (h0 : P m0) (h1 : P m1) (h2 : P m2) (h3 : P m3) (hc : P (.n c)) (hp : ∀ v, InR pad 5 v → P v)
    (ho : ∀ v, InR o 1 v → P v) : ∀ v ∈ Stmt.valsList (k64 pad m0 m1 m2 m3 c o), P v := by
  intro v hv
  rcases k64_vals pad m0 m1 m2 m3 c o hv with h | rfl | h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> assumption
  exacts [hc, hp v h, ho v h]

/-- What a level's values are: its node, a value below `103`, one of its own, or its run. -/
def LvlVal (cur : V) (b nb o : Nat) (v : V) : Prop :=
  v = cur ∨ (∃ j < 103, v = .n j) ∨ (∃ j, b ≤ j ∧ j < nb ∧ v = .n j) ∨ InR o 1 v

theorem lxLevelT_vals {w r : Nat} (hw : w < 4) (hr : r < 8) (k : Nat) (cur : V) (outO : Option Nat) {b : Nat} :
    ∀ v ∈ Stmt.valsList (lxLevelT w k r cur outO b).1,
      LvlVal cur b (lxLevelT w k r cur outO b).2.1 (lxLvlO w r outO b) v := by
  have hn : ∀ {nb o j : Nat}, j < 103 ∨ (b ≤ j ∧ j < nb) → LvlVal cur b nb o (.n j) := by
    intro nb o j h
    rcases h with h | h
    · exact Or.inr (Or.inl ⟨_, h, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨_, h.1, h.2, rfl⟩))
  have hpad : ∀ {nb o : Nat} (v : V), InR sLxPad 5 v → LvlVal cur b nb o v :=
    fun v ⟨i, hi, e⟩ => e ▸ hn (Or.inl (by simp [sLxPad]; omega))
  have hrun : ∀ {nb o : Nat} (v : V), InR o 1 v → LvlVal cur b nb o v :=
    fun v h => Or.inr (Or.inr (Or.inr h))
  have hord : ∀ {nb o s : Nat} (k' r' : Nat), LvlVal cur b nb o (.n s) →
      LvlVal cur b nb o (if k' / 2 ^ r' % 2 = 0 then (cur, V.n s) else (.n s, cur)).1 ∧
        LvlVal cur b nb o (if k' / 2 ^ r' % 2 = 0 then (cur, V.n s) else (.n s, cur)).2 := by
    intro nb o s k' r' hs
    split
    · exact ⟨Or.inl rfl, hs⟩
    · exact ⟨hs, Or.inl rfl⟩
  unfold lxLevelT lxLvlO
  by_cases hw3 : w + 1 = 4
  · simp only [hw3, ↓reduceIte]
    intro v hv
    rw [valsList_append] at hv
    rcases List.mem_append.mp hv with hv | hv
    · simp [hintW, cst, Stmt.vals, Atom.vals, Hint.vals, Dest.vals] at hv
      rcases hv with rfl | rfl <;> exact hn (Or.inr ⟨by omega, by split <;> omega⟩)
    · exact k64_vals_all (hn (Or.inl (by simp))) (hn (Or.inr ⟨by omega, by split <;> omega⟩))
        (hord _ _ (hn (Or.inr ⟨by omega, by split <;> omega⟩))).1
        (hord _ _ (hn (Or.inr ⟨by omega, by split <;> omega⟩))).2
        (hn (Or.inr ⟨by omega, by split <;> omega⟩)) hpad hrun v hv
  · simp only [hw3, ↓reduceIte]
    by_cases hr7 : r + 1 = 8
    · simp only [hr7, ↓reduceIte]
      intro v hv
      rw [valsList_append] at hv
      rcases List.mem_append.mp hv with hv | hv
      · simp [hintW, cst, addS, sHis, Stmt.vals, Atom.vals, Hint.vals, Dest.vals] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | exact hn (Or.inl (by omega)) | exact hn (Or.inr ⟨by omega, by split <;> omega⟩)
      · exact k64_vals_all (hn (Or.inl (by simp))) (hn (Or.inr ⟨by omega, by split <;> omega⟩))
          (hord _ _ (hn (Or.inr ⟨by omega, by split <;> omega⟩))).1
          (hord _ _ (hn (Or.inr ⟨by omega, by split <;> omega⟩))).2
          (hn (Or.inr ⟨by omega, by split <;> omega⟩)) hpad hrun v hv
    · simp only [hr7, ↓reduceIte]
      intro v hv
      rw [valsList_append] at hv
      rcases List.mem_append.mp hv with hv | hv
      · simp [hintW, cst, addS, mulS, sHis, sPower, Stmt.vals, Atom.vals, Hint.vals, Dest.vals] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | exact hn (Or.inl (by omega)) | exact hn (Or.inr ⟨by omega, by omega⟩)
      · exact k64_vals_all (hn (Or.inl (by simp))) (hn (Or.inr ⟨by omega, by omega⟩))
          (hord _ _ (hn (Or.inr ⟨by omega, by omega⟩))).1
          (hord _ _ (hn (Or.inr ⟨by omega, by omega⟩))).2
          (hn (Or.inr ⟨by omega, by omega⟩)) hpad hrun v hv

/-! ## The eight levels of an arm -/

/-- Where the last level of an arm of window `w` from base `b0` writes its node. -/
def lxArmO (w : Nat) (outO : Option Nat) (b0 : Nat) : Nat := lxLvlO w 7 outO (b0 + lxStride w * 7)

theorem lxArmO_cases (w : Nat) (outO : Option Nat) (b0 : Nat) :
    (∃ o, outO = some o ∧ lxArmO w outO b0 = o) ∨
      (outO = none ∧ b0 + lxStride w * 7 + 3 ≤ lxArmO w outO b0 ∧ lxArmO w outO b0 ≤ b0 + lxStride w * 7 + 4) := by
  unfold lxArmO lxLvlO
  cases outO with
  | none => right; refine ⟨rfl, ?_⟩; split <;> simp
  | some o => left; exact ⟨o, rfl, by split <;> simp⟩

theorem lxStride_ge (w : Nat) : 4 ≤ lxStride w := by unfold lxStride; split <;> omega

theorem lxLvlO_lt {w r : Nat} (hr : r + 1 ≠ 8) (outO : Option Nat) (b : Nat) :
    b + 3 ≤ lxLvlO w r outO b ∧ lxLvlO w r outO b + 1 = b + lxStride w := by
  unfold lxLvlO lxStride
  by_cases hw : w + 1 = 4 <;> simp [hw, hr]

theorem lxSibCell_lt (w r b : Nat) : b ≤ lxSibCell w r b ∧ lxSibCell w r b ≤ b + 3 := by
  unfold lxSibCell; split <;> [omega; split <;> omega]

/-- **The levels of an arm complete** by the honest arm, level `j`'s sibling `sibs j`. -/
theorem lxLevelsT_complete {L : Nat} (hL : L < 2 ^ 32) {w : Nat} (hw : w < 4) {outO : Option Nat}
    {b0 : Nat} (hb0 : 103 ≤ b0) (sibs : Nat → E) (hO : ∀ o, outO = some o → 103 ≤ o ∧ o + 1 ≤ b0) :
    ∀ m r (cur : V) b (σ : Val), r + m = 8 → b = b0 + lxStride w * r → LxEnv L σ → NBv b cur →
      (∀ o, outO = some o → ¬ InR o 1 cur) →
      CompletesO C rd b (lxLevelsT w (lxWin L w) outO m r cur b).2.1 (lxArmO w outO b0)
        (lxLevelsT w (lxWin L w) outO m r cur b).1 σ
        (fun σ' => ∀ j, r ≤ j → j < 8 → lxSibF σ' w b0 j = sibs j)
  | 0, r, cur, b, σ, hrm, _, _, _, _ =>
      ⟨σ, fun _ _ _ => rfl, fun j h1 h2 => absurd h2 (by omega), fun _ _ hn => hn⟩
  | m + 1, r, cur, b, σ, hrm, hb, hE, hcur, hcO => by
      have hr : r < 8 := by omega
      have hst := lxStride_ge w
      have hbb : b0 ≤ b := by rw [hb]; omega
      have hlv := lxLevelT_complete (C := C) (rd := rd) (L := L) (sib := sibs r) hw hr σ (by omega) hcur
        (fun o ho => ⟨(hO o ho).1, by have := (hO o ho).2; omega, hcO o ho⟩)
      have hsl := lxSibCell_lt w r b
      simp only [lxLevelsT]
      by_cases hm : m = 0
      · subst hm
        have hr7 : r = 7 := by omega
        subst hr7
        simp only [lxLevelsT, List.append_nil]
        have ho : lxArmO w outO b0 = lxLvlO w 7 outO b := by rw [lxArmO, hb]
        rw [ho]
        refine hlv.mono le_rfl le_rfl (fun σ' h1 j h1' h2' => ?_)
        obtain rfl : j = 7 := by omega
        rw [lxSibF, ← hb]
        exact h1
      · have hr7 : r + 1 ≠ 8 := by omega
        obtain ⟨hlo3, hlo13⟩ := lxLvlO_lt (w := w) hr7 outO b
        have hnb : (lxLevelT w (lxWin L w) r cur outO b).2.1 = b + lxStride w := lxLevelT_next hr7
        have hshape := (lxLevelsT_shape (w := w) (k := lxWin L w) (outO := outO) (b0 := b0) m (r + 1)
          (lxLevelT w (lxWin L w) r cur outO b).2.2 (lxLevelT w (lxWin L w) r cur outO b).2.1 (by omega)
          (by omega) (by rw [hnb, hb]; ring)).1
        have hOg := lxArmO_cases w outO b0
        have hb7 : b + lxStride w ≤ b0 + lxStride w * 7 := by
          have := Nat.mul_le_mul_left (lxStride w) (show r + 1 ≤ 7 by omega)
          rw [Nat.mul_succ] at this
          omega
        -- the level's values: below its end, off the arm's run
        have hoff : ∀ j, b ≤ j → j < b + lxStride w → ¬ InR (lxArmO w outO b0) 1 (.n j) := fun j h1 h2 =>
          notInR_of (by rcases hOg with ⟨o, ho, e⟩ | ⟨-, e1, -⟩
                        · have := (hO o ho).2; omega
                        · omega)
        have hxs : ∀ v ∈ Stmt.valsList (lxLevelT w (lxWin L w) r cur outO b).1,
            NBv (b + lxStride w) v ∧ ¬ InR (lxArmO w outO b0) 1 v := by
          intro v hv
          rcases lxLevelT_vals hw hr (lxWin L w) cur outO v hv with rfl | ⟨j, hj, rfl⟩ | ⟨j, h1, h2, rfl⟩ | ⟨i, hi, rfl⟩
          · obtain ⟨j, hj, rfl⟩ := hcur
            refine ⟨⟨j, by omega, rfl⟩, ?_⟩
            rcases hOg with ⟨o, ho, e⟩ | ⟨-, e1, -⟩
            · rw [e]; exact hcO o ho
            · exact notInR_of (by omega)
          · refine ⟨⟨j, by omega, rfl⟩, notInR_of ?_⟩
            rcases hOg with ⟨o, ho, e⟩ | ⟨-, e1, -⟩
            · have := (hO o ho).1; omega
            · omega
          · rw [hnb] at h2; exact ⟨⟨j, h2, rfl⟩, hoff j h1 h2⟩
          · exact ⟨⟨_, by omega, rfl⟩, hoff _ (by omega) (by omega)⟩
        rw [hnb] at hlv hshape
        rw [hnb]
        refine Completes.appendO (by omega) (by rw [hshape]; omega) hxs
          (hlv.toC le_rfl (by omega) le_rfl (by omega)) (fun σ1 he1 hs1 => ?_)
        have hE1 : LxEnv L σ1 := hE.congr fun j hj => he1.apply (Or.inl (by omega))
        have ih := lxLevelsT_complete hL hw hb0 sibs hO m (r + 1) (lxLevelT w (lxWin L w) r cur outO b).2.2
          (b + lxStride w) σ1 (by omega) (by rw [hb]; ring) hE1
          (by rw [lxLevelT_out]; exact ⟨_, by omega, rfl⟩)
          (fun o ho => by rw [lxLevelT_out]; exact notInR_of (by have := (hO o ho).2; omega))
        refine ih.keep.mono le_rfl le_rfl (fun σ' ⟨h1, he⟩ j hj1 hj2 => ?_)
        rcases Nat.lt_or_ge r j with hrj | hrj
        · exact h1 j hrj hj2
        · obtain rfl : j = r := by omega
          rw [lxSibF, ← hb, he.apply (Or.inl (by omega)) ?_, hs1]
          rcases hOg with ⟨o, ho, e⟩ | ⟨-, e1, -⟩
          · have := (hO o ho).2; omega
          · omega

theorem LvlVal.widen {cur : V} {b nb o b' nb' : Nat} {v : V} (h : LvlVal cur b nb o v) (hb : b' ≤ b)
    (hnb : nb ≤ nb') : LvlVal cur b' nb' o v := by
  rcases h with h | h | ⟨j, h1, h2, rfl⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl ⟨j, by omega, by omega, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr h))

theorem lxLevelT_snd_ge (w k r : Nat) (cur : V) (outO : Option Nat) (b : Nat) :
    b + 3 ≤ (lxLevelT w k r cur outO b).2.1 := by
  unfold lxLevelT
  by_cases hw : w + 1 = 4 <;> by_cases hr : r + 1 = 8 <;> cases outO <;> simp [hw, hr]

theorem lxLevelsT_snd_ge {w k : Nat} {outO : Option Nat} :
    ∀ m r (cur : V) b, b ≤ (lxLevelsT w k outO m r cur b).2.1
  | 0, _, _, _ => le_rfl
  | m + 1, r, cur, b => by
      simp only [lxLevelsT]
      exact le_trans (by have := lxLevelT_snd_ge w k r cur outO b; omega) (lxLevelsT_snd_ge m (r + 1) _ _)

/-- **The levels' values**: the arm's node, a value below `103`, one of the levels' own, or the
arm's run. -/
theorem lxLevelsT_vals {w : Nat} (hw : w < 4) (k : Nat) {outO : Option Nat} {b0 : Nat} :
    ∀ m r (cur : V) b, r + m = 8 → b = b0 + lxStride w * r →
      ∀ v ∈ Stmt.valsList (lxLevelsT w k outO m r cur b).1,
        LvlVal cur b (lxLevelsT w k outO m r cur b).2.1 (lxArmO w outO b0) v
  | 0, _, _, _, _, _ => fun v hv => by simp [lxLevelsT] at hv
  | m + 1, r, cur, b, hrm, hb => by
      intro v hv
      have hr : r < 8 := by omega
      simp only [lxLevelsT, valsList_append, List.mem_append] at hv ⊢
      have hge := lxLevelsT_snd_ge (w := w) (k := k) (outO := outO) m (r + 1)
        (lxLevelT w k r cur outO b).2.2 (lxLevelT w k r cur outO b).2.1
      have hnb : b ≤ (lxLevelT w k r cur outO b).2.1 := by
        have := lxLevelT_snd_ge w k r cur outO b; omega
      rcases hv with hv | hv
      · have h := lxLevelT_vals hw hr k cur outO v hv
        by_cases h7 : r + 1 = 8
        · obtain rfl : r = 7 := by omega
          have ho : lxArmO w outO b0 = lxLvlO w 7 outO b := by rw [lxArmO, hb]
          rw [ho]
          exact h.widen le_rfl hge
        · obtain ⟨h3, h13⟩ := lxLvlO_lt (w := w) h7 outO b
          rw [lxLevelT_next h7] at h hge ⊢
          rcases h with h | h | h | ⟨i, hi, rfl⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact LvlVal.widen (v := v) (Or.inr (Or.inr (Or.inl h))) le_rfl hge
          · exact Or.inr (Or.inr (Or.inl ⟨_, by omega, by omega, rfl⟩))
      · by_cases hm : m = 0
        · subst hm; simp [lxLevelsT] at hv
        have h := lxLevelsT_vals hw k m (r + 1) (lxLevelT w k r cur outO b).2.2
          (lxLevelT w k r cur outO b).2.1 (by omega)
          (by rw [lxLevelT_next (by omega), hb]; ring) v hv
        rcases h with rfl | h | h | h
        · rw [lxLevelT_out] at hge ⊢
          have : lxLvlO w r outO b < (lxLevelT w k r cur outO b).2.1 := by
            rw [lxLevelT_next (by omega)]; have := lxLvlO_lt (w := w) (show r + 1 ≠ 8 by omega) outO b; omega
          exact Or.inr (Or.inr (Or.inl ⟨_, by have := lxLvlO_lt (w := w) (show r + 1 ≠ 8 by omega) outO b; omega,
            lt_of_lt_of_le this hge, rfl⟩))
        · exact Or.inr (Or.inl h)
        · exact LvlVal.widen (v := v) (Or.inr (Or.inr (Or.inl h))) hnb le_rfl
        · exact Or.inr (Or.inr (Or.inr h))

/-! ## An arm -/

theorem lxArmO_eq (w : Nat) (outO : Option Nat) (b : Nat) :
    lxArmO w outO b = outO.getD (b + lxStride w * 7 + if w + 1 = 4 then 3 else 4) := by
  unfold lxArmO lxLvlO; split <;> simp_all

theorem lxArmT_vals {w : Nat} (hw : w < 4) (k : Nat) (cur : V) (outO : Option Nat) (b : Nat) :
    ∀ v ∈ Stmt.valsList (lxArmT w k cur outO b).1, LvlVal cur b (lxArmT w k cur outO b).2 (lxArmO w outO b) v := by
  intro v hv
  unfold lxArmT at hv ⊢
  by_cases hw3 : w + 1 = 4
  · have hl := lxLevelsT_vals (b0 := b) hw k (outO := outO) 8 0 cur b rfl (by simp)
    simp only [hw3, ↓reduceIte, valsList_append, List.mem_append] at hv ⊢
    rcases hv with hv | hv
    · exact hl v hv
    · simp [cst, Stmt.vals, Atom.vals] at hv; subst hv; exact Or.inr (Or.inl ⟨_, by omega, rfl⟩)
  · by_cases hk : k = 0
    · subst hk
      have hl := lxLevelsT_vals (b0 := b) hw 0 (outO := outO) 8 0 cur b rfl (by simp)
      simp only [hw3, ↓reduceIte, valsList_append, List.mem_append] at hv ⊢
      rcases hv with hv | hv
      · exact hl v hv
      · simp [mulS, sHis, sPower, Stmt.vals, Atom.vals] at hv
        rcases hv with rfl | rfl | rfl <;> exact Or.inr (Or.inl ⟨_, by omega, rfl⟩)
    · have hl := lxLevelsT_vals (b0 := b) hw k (outO := outO) 8 0 cur b rfl (by simp)
      simp only [hw3, hk, ↓reduceIte, valsList_append, List.mem_append] at hv ⊢
      rcases hv with hv | hv
      · exact (hl v hv).widen le_rfl (by omega)
      · have hge := lxLevelsT_snd_ge (w := w) (k := k) (outO := outO) 8 0 cur b
        simp [mulS, addS, cst, sHis, sPower, Stmt.vals, Atom.vals] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | exact Or.inr (Or.inl ⟨_, by omega, rfl⟩) |
            exact Or.inr (Or.inr (Or.inl ⟨_, by omega, by omega, rfl⟩))

theorem lxSibCell_last {w j : Nat} (hj : j < 8) (b : Nat) :
    lxSibCell w j (b + lxStride w * j) < b + lxStride w * 7 + 3 := by
  unfold lxSibCell lxStride
  by_cases hw : w + 1 = 4
  · simp only [hw, ↓reduceIte]; omega
  · simp only [hw, ↓reduceIte]; split <;> omega

theorem lxArmO_lt (w : Nat) (outO : Option Nat) (b : Nat)
    (hO : ∀ o, outO = some o → o + 1 ≤ b) :
    lxArmO w outO b + 1 ≤ b + lxStride w * 7 + lxLastNext w outO := by
  rw [lxArmO_eq]
  cases outO with
  | none => unfold lxLastNext; split <;> simp
  | some o => have := hO o rfl; simp only [Option.getD_some]; omega

/-- **An arm of a window completes** by the honest arm, level `j`'s sibling `sibs j`: its siblings
kept. -/
theorem lxArmT_complete {L : Nat} (hL : L < 2 ^ 32) {w : Nat} (hw : w < 4) {cur : V}
    {outO : Option Nat} {b : Nat} (σ : Val) (hE : LxEnv L σ) (hb : 103 ≤ b) (hcur : NBv b cur)
    (hO : ∀ o, outO = some o → 103 ≤ o ∧ o + 1 ≤ b ∧ ¬ InR o 1 cur) (sibs : Nat → E) :
    CompletesO C rd b (lxArmT w (lxWin L w) cur outO b).2 (lxArmO w outO b)
      (lxArmT w (lxWin L w) cur outO b).1 σ (fun σ' => ∀ j < 8, lxSibF σ' w b j = sibs j) := by
  have hlv := lxLevelsT_complete (C := C) (rd := rd) hL hw hb sibs
    (fun o ho => ⟨(hO o ho).1, (hO o ho).2.1⟩) 8 0 cur b σ rfl (by simp) hE hcur
    (fun o ho => (hO o ho).2.2)
  have hshape := lxLevelsT_shape (w := w) (k := lxWin L w) (outO := outO) (b0 := b) 8 0 cur b rfl
    (by omega) (by simp)
  have hst := lxStride_ge w
  have hOg := lxArmO_cases w outO b
  have hOe := lxArmO_lt w outO b (fun o ho => (hO o ho).2.1)
  have hO103 : 103 ≤ lxArmO w outO b := by
    rcases hOg with ⟨o, ho, e⟩ | ⟨-, e1, -⟩
    · rw [e]; exact (hO o ho).1
    · omega
  have hnum : NumBelow (lxLevelsT w (lxWin L w) outO 8 0 cur b).2.1
      (Stmt.valsList (lxLevelsT w (lxWin L w) outO 8 0 cur b).1) := by
    intro v hv
    rw [hshape.1]
    rcases lxLevelsT_vals (b0 := b) hw (lxWin L w) (outO := outO) 8 0 cur b rfl (by simp) v hv with
      rfl | ⟨j, hj, rfl⟩ | ⟨j, h1, h2, rfl⟩ | ⟨i, hi, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := hcur; exact ⟨j, by omega, rfl⟩
    · exact ⟨j, by omega, rfl⟩
    · rw [hshape.1] at h2; exact ⟨j, h2, rfl⟩
    · exact ⟨_, by omega, rfl⟩
  have hE1 : ∀ σ1, ExtO b (lxLevelsT w (lxWin L w) outO 8 0 cur b).2.1 (lxArmO w outO b) σ σ1 → LxEnv L σ1 :=
    fun σ1 he1 => hE.congr fun j hj => he1.apply (Or.inl (by omega)) (Or.inl (by omega))
  have hend : b + lxStride w * 7 + 3 ≤ (lxLevelsT w (lxWin L w) outO 8 0 cur b).2.1 := by
    rw [hshape.1]; unfold lxLastNext; split <;> split <;> omega
  -- the post, kept by the pin's values above the levels
  have hkeep : ∀ σ1 σ2, (∀ j, j < (lxLevelsT w (lxWin L w) outO 8 0 cur b).2.1 → σ2 (.n j) = σ1 (.n j)) →
      (∀ j, 0 ≤ j → j < 8 → lxSibF σ1 w b j = sibs j) → ∀ j < 8, lxSibF σ2 w b j = sibs j := by
    intro σ1 σ2 h h1 j hj
    have := lxSibCell_last (w := w) hj b
    rw [lxSibF, h _ (by omega)]
    exact h1 j (Nat.zero_le _) hj
  have hpow8 : gen ^ 8 = eOfNat (2 ^ 8) := gen_pow_eq_eOfNat (by norm_num)
  obtain ⟨hh3, hhs⟩ := lx_his_honest hL
  unfold lxArmT
  by_cases hw3 : w + 1 = 4
  · simp only [hw3, ↓reduceIte]
    obtain rfl : w = 3 := by omega
    refine CompletesO.append (by omega) le_rfl hnum hlv (fun σ1 he1 hp1 => ?_)
    have hc : (Atom.const (.n (67 + 3)) (word (lxWin L 3) 0)).Holds rd σ1 := by
      show σ1 (sHis 3) = _
      rw [(hE1 σ1 he1).2.1 3 (by omega), word_eq_eOfNat]
      exact hh3
    exact (check_complete hc _).mono le_rfl le_rfl (fun σ' e => by
      subst e; exact hkeep σ' σ' (fun _ _ => rfl) hp1)
  · simp only [hw3, ↓reduceIte]
    by_cases hk : lxWin L w = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hk)]
      refine CompletesO.append (by omega) le_rfl hnum hlv (fun σ1 he1 hp1 => ?_)
      have hc : (Atom.mul (sHis w) (sHis (w + 1)) (sPower 8)).Holds rd σ1 := by
        show σ1 (sHis w) = σ1 (sHis (w + 1)) * σ1 (sPower 8)
        have h1 := hE1 σ1 he1
        rw [h1.2.1 w (by omega), h1.2.1 (w + 1) (by omega), h1.2.2 8 (by omega), hpow8,
          hhs w (by omega), hk, eOfNat_zero, add_zero]
      exact (check_complete hc _).mono le_rfl le_rfl (fun σ' e => by
        subst e; exact hkeep σ' σ' (fun _ _ => rfl) hp1)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hk)]
      refine CompletesO.append (by omega) (by omega) hnum hlv (fun σ1 he1 hp1 => ?_)
      have h1 := hE1 σ1 he1
      rw [show ∀ (x y z : Stmt), [x, y, z] = [x, y] ++ [z] from fun _ _ _ => rfl]
      refine Completes.seq ⟨⟨rfl, ⟨_, by omega, rfl⟩, ⟨_, by omega, rfl⟩⟩, rfl, rfl⟩ le_rfl
        (fun σ2 he2 hh2 => ?_)
      have hm : σ2 (.n (lxLevelsT w (lxWin L w) outO 8 0 cur b).2.1) = σ2 (sHis (w + 1)) * σ2 (sPower 8) :=
        hh2.atom (a := .mul _ _ _) (by simp [mulS])
      have hcst : σ2 (.n ((lxLevelsT w (lxWin L w) outO 8 0 cur b).2.1 + 1)) = word (lxWin L w) 0 :=
        hh2.atom (a := .const _ _) (by simp [cst])
      have h2 : LxEnv L σ2 := h1.congr fun j hj => he2.apply (Or.inl (by omega))
      have hc : (Atom.add (sHis w) (.n (lxLevelsT w (lxWin L w) outO 8 0 cur b).2.1)
          (.n ((lxLevelsT w (lxWin L w) outO 8 0 cur b).2.1 + 1))).Holds rd σ2 := by
        show σ2 (sHis w) = σ2 (.n _) + σ2 (.n _)
        rw [hm, hcst, h2.2.1 w (by omega), h2.2.1 (w + 1) (by omega), h2.2.2 8 (by omega), hpow8,
          word_eq_eOfNat]
        exact hhs w (by omega)
      exact (check_complete hc _).mono le_rfl le_rfl (fun σ' e => by
        subst e; exact hkeep σ1 σ' (fun j hj => he2.apply (Or.inl hj)) hp1)

/-! ## A window -/

theorem lxArmB_succ (w : Nat) : ∀ j k b, lxArmB w k (j + 1) b = lxArmB w k j b + lxArmSize w (k + j)
  | 0, k, b => by simp [lxArmB]
  | j + 1, k, b => by
      rw [lxArmB, lxArmB_succ w j (k + 1) _, lxArmB, show k + 1 + j = k + (j + 1) by omega]

theorem lxArmB_mono (w k b : Nat) {j j' : Nat} (h : j ≤ j') : lxArmB w k j b ≤ lxArmB w k j' b := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [lxArmB_succ]; omega

theorem lxArmB_ge (w k j b : Nat) : b ≤ lxArmB w k j b := lxArmB_mono w k b (Nat.zero_le j)

theorem lxArmsT_snd (w : Nat) (cur : V) (o : Nat) : ∀ m k b, (lxArmsT w cur o m k b).2 = lxArmB w k m b
  | 0, _, _ => rfl
  | m + 1, k, b => by
      simp only [lxArmsT, lxArmB]
      rw [lxArmsT_snd w cur o m (k + 1), lxArmT_next']

theorem lxOut0_size (w b : Nat) : lxOut0 w b + 1 = b + lxArmSize w 0 ∧ b + 31 ≤ lxOut0 w b := by
  unfold lxOut0 lxArmSize lxStride lxLastNext
  by_cases hw : w + 1 = 4 <;> simp [hw]

theorem lxArmO_none (w b : Nat) : lxArmO w none b = lxOut0 w b := by
  rw [lxArmO_eq]; unfold lxOut0 lxStride; split <;> simp

theorem lxArmO_some (w o b : Nat) : lxArmO w (some o) b = o := by rw [lxArmO_eq]; rfl

theorem lxWindowT_snd (w : Nat) (cur : V) (b : Nat) :
    (lxWindowT w cur b).2.1 = lxArmB w 0 256 (b + 5) := by
  dsimp only [lxWindowT]
  exact lxArmsT_snd ..

/-- Where arm `k` of the window from `b` lies: its base and end below the window's end, arm `0`'s
node's run below arm `k`'s base for `k ≠ 0`. -/
theorem lxArm_place (w : Nat) {k : Nat} (hk : k < 256) (b : Nat) :
    b + 5 ≤ lxArmB w 0 k (b + 5) ∧ lxArmB w 0 k (b + 5) + lxArmSize w k ≤ lxArmB w 0 256 (b + 5) ∧
      lxOut0 w (b + 5) + 1 ≤ lxArmB w 0 256 (b + 5) ∧
      (k ≠ 0 → lxOut0 w (b + 5) + 1 ≤ lxArmB w 0 k (b + 5)) := by
  have h1 := lxArmB_succ w k 0 (b + 5)
  have h0 := lxArmB_succ w 0 0 (b + 5)
  simp only [Nat.zero_add] at h1 h0
  have hm := lxArmB_mono w 0 (b + 5) (show k + 1 ≤ 256 by omega)
  have hm1 := lxArmB_mono w 0 (b + 5) (show 1 ≤ 256 by omega)
  have hz : lxArmB w 0 0 (b + 5) = b + 5 := rfl
  have ho := (lxOut0_size w (b + 5)).1
  refine ⟨lxArmB_ge .., by omega, by omega, fun hk0 => ?_⟩
  have := lxArmB_mono w 0 (b + 5) (show 1 ≤ k by omega)
  omega

theorem lxArm_O (w k b : Nat) :
    lxArmO w (if k = 0 then none else some (lxOut0 w (b + 5))) (lxArmB w 0 k (b + 5)) = lxOut0 w (b + 5) := by
  by_cases h0 : k = 0
  · subst h0; simp only [↓reduceIte, lxArmO_none]; rfl
  · simp only [h0, ↓reduceIte, lxArmO_some]

/-- **A window completes** by the honest arm `lxWin L w`, its range check against `g^255`, level
`r`'s sibling `sibs r`: the siblings where the arm hints them. -/
theorem lxWindowT_complete (hm : MemOK rd 256) {L : Nat} (hL : L < 2 ^ 32) {w : Nat} (hw : w < 4)
    {cur : V} {b : Nat} (σ : Val) (hE : LxEnv L σ) (hwin : σ (sWin w) = ofK (addressOfIndex (lxWin L w)))
    (hb : 103 ≤ b) (hcur : NBv b cur) (sibs : Nat → E) :
    Completes C rd b (lxWindowT w cur b).2.1 (lxWindowT w cur b).1 σ
      (fun σ' => ∀ r < 8, lxSibF σ' w (lxArmB w 0 (lxWin L w) (b + 5)) r = sibs r) := by
  have hk := lxWin_lt L w
  obtain ⟨p1, p2, p3, p4⟩ := lxArm_place w hk b
  have hsw : NBv b (sWin w) := ⟨71 + w, by omega, rfl⟩
  rw [lxWindowT_snd]
  dsimp only [lxWindowT]
  rw [show ∀ (x y : Stmt), [x, y] = [x] ++ [y] from fun _ _ => rfl]
  rw [show bound255 = ofK (addressOfIndex (256 - 1)) from bound255_eq]
  refine Completes.append (m := b + 4) (by omega) (by omega) ?_
    (rangeS_complete hm le_rfl hk σ (sWin w) hsw hwin) (fun σ1 he1 _ => ?_)
  · intro v hv
    simp [rangeS, cst, Stmt.vals, Atom.vals] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨_, by omega, rfl⟩
  refine Completes.append (m := b + 5) (by omega) (by omega)
    (by simp [cst, Stmt.vals, Atom.vals]; exact .cons ⟨b + 4, by omega, rfl⟩ (.nil _))
    (cst_complete σ1 (b + 4) closeLane) (fun σ2 he2 _ => ?_)
  have hσ2 : ∀ j < b, σ2 (.n j) = σ (.n j) := fun j hj =>
    (he2.apply (Or.inl (by omega))).trans (he1.apply (Or.inl hj))
  refine match_complete (k := lxWin L w) (by rw [lxArmsT_length]; exact hk) (hsw.mono' (by omega))
    (by obtain ⟨j, hj, e⟩ := hsw; rw [e, hσ2 j hj, ← e]; exact hwin) ?_
  rw [lxArmsT_getElem]
  simp only [Nat.zero_add]
  obtain ⟨jc, hjc, rfl⟩ := hcur
  have hE2 : LxEnv L σ2 := hE.congr fun j hj => hσ2 j (by omega)
  have harm := lxArmT_complete (C := C) (rd := rd) hL hw (cur := .n jc)
    (outO := if lxWin L w = 0 then none else some (lxOut0 w (b + 5))) (b := lxArmB w 0 (lxWin L w) (b + 5))
    σ2 hE2 (by omega) ⟨jc, by omega, rfl⟩
    (fun o ho => by
      by_cases h0 : lxWin L w = 0
      · simp [h0] at ho
      · simp only [h0, ↓reduceIte, Option.some.injEq] at ho
        subst ho
        exact ⟨by have := (lxOut0_size w (b + 5)).2; omega, p4 h0,
          notInR_of (by have := (lxOut0_size w (b + 5)).2; omega)⟩) sibs
  rw [lxArm_O, lxArmT_next'] at harm
  have := (lxOut0_size w (b + 5)).2
  exact harm.toC (by omega) (by omega) p2 p3

/-- **A window's values lie below its end**, its node below its base. -/
theorem lxWindowT_numBelow {w : Nat} (hw : w < 4) {cur : V} {b : Nat} (hb : 103 ≤ b) (hcur : NBv b cur) :
    NumBelow (lxWindowT w cur b).2.1 (Stmt.valsList (lxWindowT w cur b).1) := by
  have hsw : NBv b (sWin w) := ⟨71 + w, by omega, rfl⟩
  have hend : b + 5 ≤ lxArmB w 0 256 (b + 5) := lxArmB_ge ..
  have harms : ∀ a ∈ (lxArmsT w cur (lxOut0 w (b + 5)) 256 0 (b + 5)).1,
      NumBelow (lxArmB w 0 256 (b + 5)) (Stmt.valsList a) := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
    have hk' : k < 256 := by rw [lxArmsT_length] at hk; exact hk
    rw [lxArmsT_getElem]
    simp only [Nat.zero_add]
    obtain ⟨p1, p2, p3, p4⟩ := lxArm_place w hk' b
    intro v hv
    rcases lxArmT_vals hw k cur _ _ v hv with rfl | ⟨j, hj, rfl⟩ | ⟨j, h1, h2, rfl⟩ | ⟨i, hi, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := hcur; exact ⟨j, by omega, rfl⟩
    · exact ⟨j, by omega, rfl⟩
    · rw [lxArmT_next'] at h2; exact ⟨j, by omega, rfl⟩
    · rw [lxArm_O]; exact ⟨_, by omega, rfl⟩
  rw [lxWindowT_snd]
  dsimp only [lxWindowT]
  intro v hv
  simp only [valsList_append, valsList_cons, valsList_nil, List.append_nil, List.mem_append, rangeS, cst,
    Stmt.vals, Atom.vals, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl | hv
  all_goals first | exact ⟨_, by omega, rfl⟩ | exact numBelow_valsArms _ harms v hv

/-! ## A window's node, the fold over the index -/

theorem mFold_congr' {pp : E} {A A' : Nat → E} {bits bits' : Nat → Bool} {sibs sibs' : Nat → E} :
    ∀ m l l' x, (∀ j < m, A (l + j) = A' (l' + j) ∧ bits (l + j) = bits' (l' + j) ∧ sibs (l + j) = sibs' (l' + j)) →
      mFold pp A bits sibs m l x = mFold pp A' bits' sibs' m l' x
  | 0, _, _, _, _ => rfl
  | m + 1, l, l', x, h => by
      simp only [mFold]
      obtain ⟨h1, h2, h3⟩ := h 0 (by omega)
      simp only [Nat.add_zero] at h1 h2 h3
      rw [h1, h2, h3]
      exact mFold_congr' m (l + 1) (l' + 1) _ fun j hj => by
        have := h (j + 1) (by omega)
        rwa [show l + (j + 1) = l + 1 + j by omega, show l' + (j + 1) = l' + 1 + j by omega] at this

theorem lxMFold_add (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) :
    ∀ a c l x, mFold pp A bits sibs (a + c) l x = mFold pp A bits sibs c (l + a) (mFold pp A bits sibs a l x)
  | 0, c, l, x => by simp [mFold]
  | a + 1, c, l, x => by
      rw [show a + 1 + c = (a + c) + 1 by omega]
      simp only [mFold]
      rw [lxMFold_add pp A bits sibs a c (l + 1), show l + 1 + a = l + (a + 1) by omega]

/-- **A window completes, its node the fold** of its eight levels over the index `L`: the addresses
`lxNodeAddr L w r`, the bits `8w + r` of `L`, the hinted siblings. -/
theorem lxWindowT_complete_fold (hm : MemOK rd 256) {L : Nat} (hL : L < 2 ^ 32) {w : Nat} (hw : w < 4)
    {cur : V} {b : Nat} (σ : Val) (hE : LxEnv L σ) (hwin : σ (sWin w) = ofK (addressOfIndex (lxWin L w)))
    (hb : 103 ≤ b) (hcur : NBv b cur) (sibs : Nat → E) :
    Completes C rd b (lxWindowT w cur b).2.1 (lxWindowT w cur b).1 σ
      (fun σ' => (∀ r < 8, lxSibF σ' w (lxArmB w 0 (lxWin L w) (b + 5)) r = sibs r) ∧
        σ' (.n (lxWindowT w cur b).2.2) =
          mFold (σ sLxPP) (lxNodeAddr L w) (fun r => L.testBit (8 * w + r)) sibs 8 0 (σ cur)) := by
  obtain ⟨σ', he, hs, hh⟩ := lxWindowT_complete (C := C) hm hL hw σ hE hwin hb hcur sibs
  refine ⟨σ', he, ⟨hs, ?_⟩, hh⟩
  have hlo : ∀ j < b, σ' (.n j) = σ (.n j) := fun j hj => he.apply (Or.inl hj)
  have hE' : LxEnv L σ' := hE.congr fun j hj => hlo j (by omega)
  obtain ⟨-, k, hk, hx, -, hout⟩ := lxWindowT_sound (C := C) (rd := rd) (rest := []) (next := True)
    (kret := fun _ => True) hE'.1 (by rw [List.append_nil]; exact hh True _ trivial)
  have hkk : k = lxWin L w := by
    rw [show sWin w = .n (71 + w) from rfl, hlo _ (by omega)] at hx
    rw [show sWin w = .n (71 + w) from rfl] at hwin
    rw [hwin] at hx
    have := lxWin_lt L w
    exact (gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega)
      (ofK_injective hx)).symm
  subst hkk
  obtain ⟨jc, hjc, rfl⟩ := hcur
  rw [hout, show sLxPP = .n 66 from rfl, hlo 66 (by omega), hlo jc hjc]
  refine mFold_congr' 8 0 0 _ fun j hj => ⟨?_, ?_, ?_⟩
  · simp only [Nat.zero_add, lxAtF]
    rw [hE'.2.2 (7 - j) (by omega), gen_pow_eq_eOfNat (by omega)]
    exact lx_at hL (his := fun v => σ' (sHis v)) hE'.2.1 hw hj
  · simp [lxBitF, lx_bit L w j hj]
  · simp only [Nat.zero_add]; exact hs j hj

/-! ## A layer's two windows -/

/-- The address of level `l` of layer `layer`'s path over the index `L`. -/
def lxLayerA (L layer l : Nat) : E := lxNodeAddr L (2 * layer + l / 8) (l % 8)

/-- The bit of level `l` of layer `layer`'s path: bit `16 · layer + l` of the index. -/
def lxLayerBit (L layer l : Nat) : Bool := L.testBit (16 * layer + l)

theorem lxArmSize_ge (w k : Nat) : lxStride w * 7 + 3 ≤ lxArmSize w k := by
  unfold lxArmSize lxLastNext
  by_cases hw : w + 1 = 4 <;> by_cases hk : k = 0 <;> simp [hw, hk]

/-- **A layer's two windows complete** (`2 · layer`, then `2 · layer + 1` on its node), the hinted
siblings `sibs l` of its sixteen levels where the arms hint them: the node is the layer's path fold
`xFold` over the index. -/
theorem lxWindows_complete (hm : MemOK rd 256) {L : Nat} (hL : L < 2 ^ 32) {layer : Nat} (hlay : layer < 2)
    {cur : V} {b0 : Nat} (σ : Val) (hE : LxEnv L σ)
    (hwin : ∀ w < 4, σ (sWin w) = ofK (addressOfIndex (lxWin L w))) (hb : 103 ≤ b0) (hcur : NBv b0 cur)
    (sibs : Nat → E) :
    Completes C rd b0
      (lxWindowT (2 * layer + 1) (.n (lxWindowT (2 * layer) cur b0).2.2) (lxWindowT (2 * layer) cur b0).2.1).2.1
      ((lxWindowT (2 * layer) cur b0).1 ++
        (lxWindowT (2 * layer + 1) (.n (lxWindowT (2 * layer) cur b0).2.2) (lxWindowT (2 * layer) cur b0).2.1).1) σ
      (fun σ' => (∀ r < 8, lxSibF σ' (2 * layer) (lxArmB (2 * layer) 0 (lxWin L (2 * layer)) (b0 + 5)) r = sibs r ∧
          lxSibF σ' (2 * layer + 1) (lxArmB (2 * layer + 1) 0 (lxWin L (2 * layer + 1))
            ((lxWindowT (2 * layer) cur b0).2.1 + 5)) r = sibs (8 + r)) ∧
        σ' (.n (lxWindowT (2 * layer + 1) (.n (lxWindowT (2 * layer) cur b0).2.2)
            (lxWindowT (2 * layer) cur b0).2.1).2.2) =
          xFold (σ sLxPP) (lxLayerA L layer) (lxLayerBit L layer) sibs 16 (σ cur)) := by
  set W0 := lxWindowT (2 * layer) cur b0 with hW0
  have hw0 : 2 * layer < 4 := by omega
  have hw1 : 2 * layer + 1 < 4 := by omega
  have hk0 := lxWin_lt L (2 * layer)
  obtain ⟨p1, p2, p3, p4⟩ := lxArm_place (2 * layer) hk0 b0
  have hend0 : W0.2.1 = lxArmB (2 * layer) 0 256 (b0 + 5) := lxWindowT_snd ..
  have hout0 : W0.2.2 = lxOut0 (2 * layer) (b0 + 5) := rfl
  have h103 := (lxOut0_size (2 * layer) (b0 + 5)).2
  have hend1 := lxArmB_ge (2 * layer + 1) 0 256 (W0.2.1 + 5)
  rw [← lxWindowT_snd (2 * layer + 1) (.n W0.2.2) W0.2.1] at hend1
  refine Completes.append (m := W0.2.1) (by omega) (by omega) (lxWindowT_numBelow hw0 hb hcur)
    (lxWindowT_complete_fold (C := C) hm hL hw0 σ hE (hwin _ hw0) hb hcur sibs)
    (fun σ1 he1 ⟨hs0, hv0⟩ => ?_)
  have hlo1 : ∀ j < b0, σ1 (.n j) = σ (.n j) := fun j hj => he1.apply (Or.inl hj)
  have hE1 : LxEnv L σ1 := hE.congr fun j hj => hlo1 j (by omega)
  have hW02 : W0.2.2 < W0.2.1 := by omega
  have hW01 : 103 ≤ W0.2.1 := by omega
  obtain ⟨σ2, he2, ⟨hs1, hv1⟩, hh2⟩ := lxWindowT_complete_fold (C := C) (cur := .n W0.2.2) (b := W0.2.1)
    hm hL hw1 σ1 hE1
    (by rw [show sWin (2 * layer + 1) = .n (71 + (2 * layer + 1)) from rfl, hlo1 _ (by omega)];
        exact hwin _ hw1) hW01 ⟨W0.2.2, hW02, rfl⟩ (fun r => sibs (8 + r))
  refine ⟨σ2, he2, ⟨fun r hr => ⟨?_, hs1 r hr⟩, ?_⟩, hh2⟩
  · have hc := lxSibCell_last (w := 2 * layer) hr (lxArmB (2 * layer) 0 (lxWin L (2 * layer)) (b0 + 5))
    have := lxArmSize_ge (2 * layer) (lxWin L (2 * layer))
    have hlt : lxSibCell (2 * layer) r (lxArmB (2 * layer) 0 (lxWin L (2 * layer)) (b0 + 5) +
        lxStride (2 * layer) * r) < W0.2.1 := by omega
    rw [lxSibF, he2.apply (Or.inl hlt)]
    exact hs0 r hr
  · rw [hv1, hv0, show sLxPP = .n 66 from rfl, hlo1 66 (by omega), ← mFold_eq_xFold,
      show 16 = 8 + 8 from rfl, lxMFold_add]
    have e0 : ∀ x, mFold (σ (.n 66)) (lxLayerA L layer) (lxLayerBit L layer) sibs 8 0 x =
        mFold (σ (.n 66)) (lxNodeAddr L (2 * layer)) (fun r => L.testBit (8 * (2 * layer) + r)) sibs 8 0 x :=
      fun x => mFold_congr' 8 0 0 x fun j hj => ⟨by
          show lxNodeAddr L (2 * layer + (0 + j) / 8) ((0 + j) % 8) = lxNodeAddr L (2 * layer) (0 + j)
          rw [show (0 + j) / 8 = 0 by omega, show (0 + j) % 8 = 0 + j by omega, Nat.add_zero], by
          show L.testBit (16 * layer + (0 + j)) = L.testBit (8 * (2 * layer) + (0 + j))
          rw [show 16 * layer + (0 + j) = 8 * (2 * layer) + (0 + j) by omega], rfl⟩
    have e1 : ∀ x, mFold (σ (.n 66)) (lxLayerA L layer) (lxLayerBit L layer) sibs 8 (0 + 8) x =
        mFold (σ (.n 66)) (lxNodeAddr L (2 * layer + 1)) (fun r => L.testBit (8 * (2 * layer + 1) + r))
          (fun r => sibs (8 + r)) 8 0 x :=
      fun x => mFold_congr' 8 (0 + 8) 0 x fun j hj => ⟨by
          show lxNodeAddr L (2 * layer + (0 + 8 + j) / 8) ((0 + 8 + j) % 8) = lxNodeAddr L (2 * layer + 1) (0 + j)
          rw [show (0 + 8 + j) / 8 = 1 by omega, show (0 + 8 + j) % 8 = 0 + j by omega], by
          show L.testBit (16 * layer + (0 + 8 + j)) = L.testBit (8 * (2 * layer + 1) + (0 + j))
          rw [show 16 * layer + (0 + 8 + j) = 8 * (2 * layer + 1) + (0 + j) by omega], by
          show sibs (0 + 8 + j) = sibs (8 + (0 + j))
          rw [show 0 + 8 + j = 8 + (0 + j) by omega]⟩
    rw [e1, e0]

/-- A window's node lies between its base and its end. -/
theorem lxWindowT_out_lt (w : Nat) (cur : V) (b : Nat) :
    b + 36 ≤ (lxWindowT w cur b).2.2 ∧ (lxWindowT w cur b).2.2 + 1 ≤ (lxWindowT w cur b).2.1 := by
  rw [lxWindowT_snd, show (lxWindowT w cur b).2.2 = lxOut0 w (b + 5) from rfl]
  have := (lxOut0_size w (b + 5)).2
  exact ⟨by omega, (lxArm_place w (show 0 < 256 by norm_num) b).2.2.1⟩

/-- **A layer's two windows' values lie below their end.** -/
theorem lxWindows_numBelow {layer : Nat} (hlay : layer < 2) {cur : V} {b0 : Nat} (hb : 103 ≤ b0)
    (hcur : NBv b0 cur) :
    NumBelow
      (lxWindowT (2 * layer + 1) (.n (lxWindowT (2 * layer) cur b0).2.2) (lxWindowT (2 * layer) cur b0).2.1).2.1
      (Stmt.valsList ((lxWindowT (2 * layer) cur b0).1 ++
        (lxWindowT (2 * layer + 1) (.n (lxWindowT (2 * layer) cur b0).2.2) (lxWindowT (2 * layer) cur b0).2.1).1)) := by
  obtain ⟨h1, h2⟩ := lxWindowT_out_lt (2 * layer) cur b0
  obtain ⟨h3, h4⟩ := lxWindowT_out_lt (2 * layer + 1) (.n (lxWindowT (2 * layer) cur b0).2.2)
    (lxWindowT (2 * layer) cur b0).2.1
  rw [valsList_append]
  exact ((lxWindowT_numBelow (by omega) hb hcur).mono (by omega)).append
    (lxWindowT_numBelow (by omega) (by omega) ⟨_, by omega, rfl⟩)

/-- A window's hinted siblings lie below its end. -/
theorem lxSibCell_window {w k r : Nat} (hk : k < 256) (hr : r < 8) (cur : V) (b : Nat) :
    lxSibCell w r (lxArmB w 0 k (b + 5) + lxStride w * r) < (lxWindowT w cur b).2.1 := by
  have hc := lxSibCell_last (w := w) hr (lxArmB w 0 k (b + 5))
  have := lxArmSize_ge w k
  have := (lxArm_place w hk b).2.1
  rw [lxWindowT_snd]
  omega

/-- **The path windows' completeness** (`LxWindowsC`, `XmssSegWinSpec`). -/
theorem lxWindowsC : LxWindowsC := by
  intro C rd layer hlay cur b0 L hm hL hcur hb
  obtain ⟨h1, h2⟩ := lxWindowT_out_lt (2 * layer) cur b0
  obtain ⟨h3, h4⟩ := lxWindowT_out_lt (2 * layer + 1) (.n (lxWindowT (2 * layer) cur b0).2.2)
    (lxWindowT (2 * layer) cur b0).2.1
  refine ⟨by omega, lxWindows_numBelow hlay hb hcur, fun σ hpad hhis hwin hpow sibs => ?_⟩
  refine (lxWindows_complete (C := C) hm hL hlay σ ⟨hpad, hhis, hpow⟩ hwin hb hcur sibs).mono
    le_rfl le_rfl (fun σ' ⟨hs, _⟩ σ'' hag => ⟨fun r hr => ?_, fun r hr => ?_⟩)
  · have := lxSibCell_window (w := 2 * layer) (lxWin_lt L (2 * layer)) hr cur b0
    rw [lxSibOf, lxSibF, ← hag _ (by omega)]
    exact (hs r hr).1
  · have := lxSibCell_window (w := 2 * layer + 1) (lxWin_lt L (2 * layer + 1)) hr
      (.n (lxWindowT (2 * layer) cur b0).2.2) (lxWindowT (2 * layer) cur b0).2.1
    rw [lxSibOf, lxSibF, ← hag _ this]
    exact (hs r hr).2

end
end LeanVM.Guest.B1.Sig
