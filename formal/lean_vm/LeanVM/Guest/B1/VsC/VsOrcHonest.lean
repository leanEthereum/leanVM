/-
  LeanVM.Guest.B1.VsC.VsOrcHonest

  The honest oracle's shared pieces: the evaluator's memory congruence modulo the range checks'
  temporaries, the overlay memory, and the honest rule by index.
-/

module

public import LeanVM.Guest.B1.VsC.OrcFix
public import LeanVM.Guest.B1.VsC.VsOrcFront

/-!
# The honest oracle's shared pieces

**The memory congruence** (`ev_congr`, `vsVal_congr`): `Fwd.ev` reads the memory only in fresh loads and
in range checks' temporaries (`congL`: no atom names a temporary, no `touch`). On two memories agreeing at
every fresh load's cell (`freshLoads`, read at the first memory's valuation), the words agree off the
temporaries (`AgreeOff`), so `verify_sub`'s values agree at every index that is no temporary of `vsRcs`.
This is what the overlay `rd0 = rdSet rd1 cells` (`w32`'s twelve stores into `.n 19`, which no fresh load
of the body reads) needs: `vsVal rd0 w args = vsVal rd1 w args` off the temporaries, which `rdOver` re-reads
per memory anyway.

**The honest rule** (`vsRule`): an oracle word by index, as `w := fixW (vsΦ rd1 args) (vsRule cur p ret)`:
the `HeapBuf` bases (`vsAllocIdx`, bumped from `cur` by `vsAllocSz p`), the stream's chunk count
`w 42 = g^p`, the three grinds' windows (`gcWin`, read off the grinded word below them), and every other
word (the callees' returns, the siblings' tail) by the rule `ret`, a parameter each phase fixes. A causal
`ret` makes `vsRule` causal (`vsRule_causal`), so `vsW_eq` is `vsFix_eq`. `fixW_congr`: rules agreeing below
`N` give oracles agreeing below `N`, so a phase's words do not depend on the later phases' rules.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Node
open LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Words agreeing off the temporaries -/

/-- Index `i` is one of the temporaries the pairs `rc` name. -/
def tIdx (rc : List (V × V)) (i : ℕ) : Bool := rc.any fun q => q.1.idx == i

/-- Words of equal length agreeing at every index that is no temporary. -/
def AgreeOff (rc : List (V × V)) (l l' : List E) : Prop :=
  l.length = l'.length ∧ ∀ i, tIdx rc i = false → l.getD i 0 = l'.getD i 0

theorem AgreeOff.refl (rc : List (V × V)) (l : List E) : AgreeOff rc l l := ⟨rfl, fun _ _ => rfl⟩

theorem AgreeOff.val {rc : List (V × V)} {l l' : List E} (h : AgreeOff rc l l') {v : V}
    (hv : tIdx rc v.idx = false) : B1.Val.ofArgs l v = B1.Val.ofArgs l' v :=
  h.2 _ hv

theorem agreeOff_append {rc : List (V × V)} {l l' m m' : List E} (hA : AgreeOff rc l l')
    (hm : m.length = m'.length) (hj : ∀ j, tIdx rc (l.length + j) = false → m.getD j 0 = m'.getD j 0) :
    AgreeOff rc (l ++ m) (l' ++ m') := by
  refine ⟨by simp [hA.1, hm], fun i hi => ?_⟩
  by_cases h : i < l.length
  · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (hA.1 ▸ h)]
    exact hA.2 i hi
  · have h1 := hA.1
    obtain ⟨j, rfl⟩ : ∃ j, i = l.length + j := ⟨i - l.length, by omega⟩
    rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), ← hA.1,
      Nat.add_sub_cancel_left]
    exact hj j hi

theorem agreeOff_padZ {rc : List (V × V)} {l l' : List E} (hA : AgreeOff rc l l') (n : ℕ) :
    AgreeOff rc (padZ l n) (padZ l' n) :=
  agreeOff_append hA (by simp [hA.1]) fun _ _ => by rw [hA.1]

/-! ## The congruence of the evaluator -/

/-- A statement the congruence takes at the counter `c`: an atom naming no temporary, no `touch`, a
range check's new temporaries among the temporaries. -/
def congS (rc : List (V × V)) (c : ℕ) : Stmt → Bool
  | .atom a => (atomUses a).all (fun v => !tIdx rc v.idx) &&
      match a with
      | .rangeCheck _ y _ _ _ =>
          if isN c y then tIdx rc (c + 1) && tIdx rc (c + 2) else tIdx rc c && tIdx rc (c + 1)
      | .touch .. => false
      | _ => true
  | _ => true

/-- `congS` along a block, the counter as the checker moves it. -/
def congL (rc : List (V × V)) : ℕ → List Stmt → Bool
  | _, [] => true
  | c, s :: ss => congS rc c s && congL rc ((Fwd.chkS c s).getD c) ss

/-- A statement's fresh load, at the counter `c`. -/
def freshHd (c : ℕ) : Stmt → List Atom
  | .atom (.load d p off) => if isN c d then [.load d p off] else []
  | _ => []

/-- **A block's fresh loads**: the loads that define a new value, reading the memory. -/
def freshLoads : ℕ → List Stmt → List Atom
  | _, [] => []
  | c, s :: ss => freshHd c s ++ freshLoads ((Fwd.chkS c s).getD c) ss

theorem chkS_load_old {c c1 : ℕ} {d p : V} {off : ℕ} (h : Fwd.chkS c (.atom (.load d p off)) = some c1) :
    p.idx < c := by
  simp only [Fwd.chkS, chkA] at h
  by_cases h1 : oldB c p = true
  · simp only [oldB, Bool.and_eq_true, decide_eq_true_eq] at h1
    exact h1.2
  · simp [h1] at h

section
variable {rc : List (V × V)} {rd rd' : Reader} {w : ℕ → E}

/-- **One statement's new words agree off the temporaries.** -/
theorem newS_congr {l l' : List E} {s : Stmt} (hA : AgreeOff rc l l') (hc : congS rc l.length s = true)
    (hfr : ∀ d p off, s = .atom (.load d p off) → isN l.length d = true →
      rdAt rd (B1.Val.ofArgs l p) off = rdAt rd' (B1.Val.ofArgs l p) off) :
    (newS rd w l s).length = (newS rd' w l' s).length ∧
      ∀ j, tIdx rc (l.length + j) = false → (newS rd w l s).getD j 0 = (newS rd' w l' s).getD j 0 := by
  have hl := hA.1
  suffices h : newS rd w l s = newS rd' w l' s ∨ ((newS rd w l s).length = (newS rd' w l' s).length ∧
      ∀ j, tIdx rc (l.length + j) = false → (newS rd w l s).getD j 0 = (newS rd' w l' s).getD j 0) by
    rcases h with h | h
    · exact ⟨by rw [h], fun j _ => by rw [h]⟩
    · exact h
  cases s with
  | atom a =>
    simp only [congS, Bool.and_eq_true, List.all_eq_true] at hc
    obtain ⟨hu, hk⟩ := hc
    have hσ : ∀ v ∈ atomUses a, B1.Val.ofArgs l v = B1.Val.ofArgs l' v := fun v hv =>
      hA.2 _ (by simpa using hu v hv)
    cases a with
    | load d p off =>
      left
      simp only [newS, newA, ← hl]
      split_ifs with h
      · rw [hfr d p off rfl h, hσ p (by simp [atomUses])]
      · rfl
    | rangeCheck x y t1 t2 k =>
      right
      have ex := hσ x (by simp [atomUses])
      have ey := hσ y (by simp [atomUses])
      have ek := hσ k (by simp [atomUses])
      simp only [newS, newA, ← hl]
      dsimp only at hk
      split_ifs at hk ⊢ with h
      · rw [Bool.and_eq_true] at hk
        refine ⟨by simp, fun j hj => ?_⟩
        match j, hj with
        | 0, _ => simp [ex, ek]
        | 1, hj => exact absurd (hk.1.symm.trans hj) (by decide)
        | 2, hj => exact absurd (hk.2.symm.trans hj) (by decide)
        | _ + 3, _ => simp
      · rw [Bool.and_eq_true] at hk
        refine ⟨by simp, fun j hj => ?_⟩
        match j, hj with
        | 0, hj => exact absurd (hk.1.symm.trans hj) (by decide)
        | 1, hj => exact absurd (hk.2.symm.trans hj) (by decide)
        | 2, _ => simp [ex, ey]
        | _ + 3, _ => simp
    | keccak ins outs i o =>
      left
      simp only [newS, newA]
      rw [List.map_congr_left (fun v hv => hσ v (by simp [atomUses, hv]))]
    | touch t p => simp at hk
    | hint h =>
      left
      cases h with
      | witness _ d => cases d <;> simp [newS, newA, hl]
      | bits _ _ _ d => cases d <;> simp [newS, newA, hl]
      | bitsExp _ _ d => cases d <;> simp [newS, newA, hl]
      | digitsExp _ _ _ _ _ _ d => cases d <;> simp [newS, newA, hl]
      | windowsExp _ _ _ _ d => cases d <;> simp [newS, newA, hl]
      | limbs v ds => simp [newS, newA, hσ v (by simp [atomUses, hintUses])]
      | inverse x d => simp [newS, newA, hσ x (by simp [atomUses, hintUses])]
      | log2Ceil _ _ _ _ => simp [newS, newA, hl]
      | alloc _ _ => simp [newS, newA, hl]
      | allocDyn _ _ => simp [newS, newA, hl]
    | const d e => left; rfl
    | add d x y =>
      left
      simp only [newS, newA]
      rw [hσ x (by simp [atomUses]), hσ y (by simp [atomUses])]
    | mul d x y =>
      left
      simp only [newS, newA, hl]
      rw [hσ x (by simp [atomUses]), hσ y (by simp [atomUses]), hσ d (by simp [atomUses])]
    | copy d x =>
      left
      simp only [newS, newA]
      rw [hσ x (by simp [atomUses])]
    | assertEq _ _ => left; rfl
    | assertInK _ _ => left; rfl
    | assertNe x i p =>
      left
      simp only [newS, newA]
      rw [hσ x (by simp [atomUses])]
    | frameAddr p run => left; simp [newS, newA, hl]
  | call _ _ rets => left; simp [newS, hl]
  | dispatch _ _ _ rets => left; simp [newS, hl]
  | _ => left; rfl

/-- **The evaluator's memory congruence**: on two memories agreeing at every fresh load's cell (read at
`L`, any extension of the first memory's words), the words agree off the temporaries. -/
theorem ev_congr : ∀ (ss : List Stmt) (l l' : List E) {c' : ℕ} (L : List E), chk l.length ss = some c' →
    congL rc l.length ss = true → AgreeOff rc l l' → (∃ m, L = ev rd w l ss ++ m) →
    (∀ a ∈ freshLoads l.length ss, ∀ d p off, a = .load d p off →
      rdAt rd (B1.Val.ofArgs L p) off = rdAt rd' (B1.Val.ofArgs L p) off) →
    AgreeOff rc (ev rd w l ss) (ev rd' w l' ss)
  | [], _, _, _, _, _, _, hA, _, _ => hA
  | s :: ss, l, l', c', L, h, hc, hA, hL, hfr => by
    simp only [chk] at h
    split at h
    · rename_i c1 hc1
      simp only [congL, Bool.and_eq_true, hc1, Option.getD_some] at hc
      obtain ⟨hlen, -, -⟩ := stepS rd w l hc1
      have hev : ev rd w l (s :: ss) = ev rd w (l ++ newS rd w l s) ss := rfl
      have hfr0 : ∀ d p off, s = .atom (.load d p off) → isN l.length d = true →
          rdAt rd (B1.Val.ofArgs l p) off = rdAt rd' (B1.Val.ofArgs l p) off := by
        intro d p off hs hd
        subst hs
        have hp := chkS_load_old hc1
        have hm : Atom.load d p off ∈ freshLoads l.length (.atom (.load d p off) :: ss) := by
          simp [freshLoads, freshHd, hd]
        have e := hfr _ hm d p off rfl
        obtain ⟨m, hm⟩ := hL
        obtain ⟨m', hm'⟩ := ev_ext rd w (.atom (.load d p off) :: ss) l
        rw [hm, hm', List.append_assoc, ofArgs_old hp] at e
        exact e
      obtain ⟨e1, e2⟩ := newS_congr (w := w) hA hc.1 hfr0
      rw [hev, show ev rd' w l' (s :: ss) = ev rd' w (l' ++ newS rd' w l' s) ss from rfl]
      refine ev_congr ss _ _ L (by rw [hlen]; exact h) (by rw [hlen]; exact hc.2)
        (agreeOff_append hA e1 e2) (by rw [← hev]; exact hL) fun a ha => hfr a ?_
      simp only [freshLoads, hc1, Option.getD_some, List.mem_append]
      exact .inr (by rw [← hlen]; exact ha)
    · cases h

end

/-! ## `verify_sub`'s values agree off the temporaries -/

/-- **`verify_sub`'s fresh loads read alike** on `rd` and `rd'`, at `rd`'s valuation, each branch's
arm when taken. -/
def VsFresh (rd rd' : Reader) (w : ℕ → E) (args : List E) : Prop :=
  let F : ℕ → List Stmt → Prop := fun c ss => ∀ a ∈ freshLoads c ss, ∀ d p off, a = .load d p off →
    rdAt rd (vsVal rd w args p) off = rdAt rd' (vsVal rd w args p) off
  F 6 vsAf ∧ (vsVal rd w args (.n 234) ≠ 0 → F 235 vsI1f) ∧ F 240 vsB ∧
    (vsVal rd w args (.n 471) = 0 → F 472 vsI2z) ∧ (vsVal rd w args (.n 471) ≠ 0 → F 477 vsI2n) ∧ F 482 vsC

/-- The congruence's kernel checks on `verify_sub`'s parts. -/
noncomputable def vsCongOk : Bool :=
  congL vsRcL 6 (vsA.map fixS) && congL vsRcL 235 vsI1f && congL vsRcL 240 vsB && congL vsRcL 472 vsI2z &&
    congL vsRcL 477 vsI2n && congL vsRcL 482 vsC && !tIdx vsRcL 234 && !tIdx vsRcL 471

set_option maxRecDepth 200000 in
theorem vsCongOk_true : vsCongOk = true := by decide +kernel

theorem vsCong_parts : congL vsRcs 6 vsAf = true ∧ congL vsRcs 235 vsI1f = true ∧ congL vsRcs 240 vsB = true ∧
    congL vsRcs 472 vsI2z = true ∧ congL vsRcs 477 vsI2n = true ∧ congL vsRcs 482 vsC = true ∧
    tIdx vsRcs 234 = false ∧ tIdx vsRcs 471 = false := by
  have h := vsCongOk_true
  simp only [vsCongOk, Bool.and_eq_true, Bool.not_eq_true'] at h
  rw [vsRcs_eq]
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

section
variable {rd rd' : Reader} {w : ℕ → E} {args : List E}

/-- **`verify_sub`'s words agree off the temporaries** on two memories its fresh loads read alike. -/
theorem vsEv_congr (ha : args.length = 6) (hf : VsFresh rd rd' w args) :
    AgreeOff vsRcs (vsEv rd w args) (vsEv rd' w args) := by
  obtain ⟨cA, cI1, cB, cI2z, cI2n, cC, t234, t471⟩ := vsCong_parts
  obtain ⟨fA, fI1, fB, fI2z, fI2n, fC⟩ := hf
  have l1 := (vsL1_spec (rd := rd) (w := w) ha).1
  have l2 := (vsL2_spec (rd := rd) (w := w) ha).1
  have l3 := (vsL3_spec (rd := rd) (w := w) ha).1
  have a1 : AgreeOff vsRcs (vsL1 rd w args) (vsL1 rd' w args) :=
    ev_congr vsAf args args (vsEv rd w args) (by rw [ha]; exact chk_vsA) (by rw [ha]; exact cA) (AgreeOff.refl _ _)
      (vsEv_ext1 ha) (by rw [ha]; exact fA)
  have s234 : B1.Val.ofArgs (vsL1 rd w args) (.n 234) = B1.Val.ofArgs (vsL1 rd' w args) (.n 234) :=
    a1.val t234
  have a2 : AgreeOff vsRcs (vsL2 rd w args) (vsL2 rd' w args) := by
    unfold vsL2
    rw [← s234]
    split_ifs with h
    · exact agreeOff_padZ a1 _
    · have e2 : vsL2 rd w args = ev rd w (vsL1 rd w args) vsI1f := by simp only [vsL2, h, ↓reduceIte]
      exact ev_congr vsI1f _ _ (vsEv rd w args) (by rw [l1]; exact chk_vsI1n) (by rw [l1]; exact cI1) a1
        (by rw [← e2]; exact vsEv_ext2 ha) (by rw [l1]; exact fI1 (by rw [vsVal_234 ha]; exact h))
  have a3 : AgreeOff vsRcs (vsL3 rd w args) (vsL3 rd' w args) :=
    ev_congr vsB _ _ (vsEv rd w args) (by rw [l2]; exact chk_vsB) (by rw [l2]; exact cB) a2 (vsEv_ext3 ha) (by rw [l2]; exact fB)
  have s471 : B1.Val.ofArgs (vsL3 rd w args) (.n 471) = B1.Val.ofArgs (vsL3 rd' w args) (.n 471) :=
    a3.val t471
  have a4 : AgreeOff vsRcs (vsL4 rd w args) (vsL4 rd' w args) := by
    unfold vsL4
    rw [← s471]
    split_ifs with h
    · have e4 : vsL4 rd w args = padZ (ev rd w (vsL3 rd w args) vsI2z) 482 := by simp only [vsL4, h, ↓reduceIte]
      obtain ⟨m, hm⟩ := vsEv_ext4 (rd := rd) (w := w) ha
      refine agreeOff_padZ (ev_congr vsI2z _ _ (vsEv rd w args) (by rw [l3]; exact chk_vsI2z) (by rw [l3]; exact cI2z) a3
        ⟨List.replicate (482 - (ev rd w (vsL3 rd w args) vsI2z).length) 0 ++ m, by rw [hm, e4, padZ, List.append_assoc]⟩
        (by rw [l3]; exact fI2z (by rw [vsVal_471 ha]; exact h))) _
    · have e4 : vsL4 rd w args = ev rd w (padZ (vsL3 rd w args) 477) vsI2n := by simp only [vsL4, h, ↓reduceIte]
      have hp : (padZ (vsL3 rd w args) 477).length = 477 := padZ_length (by omega)
      exact ev_congr vsI2n _ _ (vsEv rd w args) (by rw [hp]; exact chk_vsI2n) (by rw [hp]; exact cI2n) (agreeOff_padZ a3 _)
        (by rw [← e4]; exact vsEv_ext4 ha) (by rw [hp]; exact fI2n (by rw [vsVal_471 ha]; exact h))
  have l4 := (vsL4_spec (rd := rd) (w := w) ha).1
  exact ev_congr vsC _ _ (vsEv rd w args) (by rw [l4]; exact chk_vsC) (by rw [l4]; exact cC) a4 ⟨[], by rw [List.append_nil]; rfl⟩
    (by rw [l4]; exact fC)

/-- **`verify_sub`'s values agree off the temporaries** on two memories its fresh loads read alike. -/
theorem vsVal_congr (ha : args.length = 6) (hf : VsFresh rd rd' w args) {v : V} (hv : tIdx vsRcs v.idx = false) :
    vsVal rd w args v = vsVal rd' w args v :=
  (vsEv_congr ha hf).val hv

end

/-! ## The overlay memory -/

/-- `rd` with the cells `cells` (an index and its word) written over it, the first entry of an index first. -/
noncomputable def rdSet (rd : Reader) (cells : List (ℕ × E)) : Reader := fun a =>
  ((cells.find? fun q => decide (addressOfIndex q.1 = a)).map Prod.snd).or (rd a)

/-! ## Fixpoints of rules agreeing below `N` -/

theorem fixList_congr {Φ : (ℕ → E) → ℕ → E} {F F' : ℕ → (ℕ → E) → E} {N : ℕ}
    (h : ∀ i < N, ∀ σ, F i σ = F' i σ) : ∀ n ≤ N, fixList Φ F n = fixList Φ F' n
  | 0, _ => rfl
  | n + 1, hn => by
    rw [fixList, fixList, fixList_congr h n (by omega), h n (by omega)]

/-- **Rules agreeing below `N` give oracles agreeing below `N`.** -/
theorem fixW_congr {Φ : (ℕ → E) → ℕ → E} {F F' : ℕ → (ℕ → E) → E} {N : ℕ}
    (h : ∀ i < N, ∀ σ, F i σ = F' i σ) {i : ℕ} (hi : i < N) : fixW Φ F i = fixW Φ F' i := by
  unfold fixW
  rw [fixList_congr h (i + 1) (by omega)]

/-! ## The honest rule -/

/-- The values `verify_sub`'s `HeapBuf`s define, in order: the eighteen fixed buffers, the stream, the
sizes, the eight-word buffer, and `wC`'s three. -/
def vsAllocIdx : List ℕ :=
  [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 55, 56, 112, 3039, 3040, 3553]

/-- Their sizes, the stream's `256 p` words for `p` chunks. -/
def vsAllocSz (p : ℕ) : List ℕ := vsSz0 ++ [256 * p, 6, 8, 16, 64, 64]

/-- **The honest rule**: a `HeapBuf`'s base from `cur`, the chunk count `g^p`, the three grinds' windows
of the grinded words `.n 500`, `.n 574`, `.n 2931`, every other word by `ret`. -/
noncomputable def vsRule (cur p : ℕ) (ret : ℕ → (ℕ → E) → E) : ℕ → (ℕ → E) → E := fun i σ =>
  if i ∈ vsAllocIdx then ofK (addressOfIndex ((bases cur (vsAllocSz p)).getD (vsAllocIdx.idxOf i) 0))
  else if i = 42 then gen ^ p
  else if 512 ≤ i ∧ i ≤ 516 then gcWin 15 (σ 500) (i - 512)
  else if 581 ≤ i ∧ i ≤ 586 then gcWin 2 (σ 574) (i - 581)
  else if 2943 ≤ i ∧ i ≤ 2947 then gcWin 13 (σ 2931) (i - 2943)
  else ret i σ

theorem vsRule_causal {cur p : ℕ} {ret : ℕ → (ℕ → E) → E} (hr : CausalRule ret) :
    CausalRule (vsRule cur p ret) := by
  intro i σ σ' h
  unfold vsRule
  split_ifs with h1 h2 h3 h4 h5
  · rfl
  · rfl
  · rw [h 500 (by omega)]
  · rw [h 574 (by omega)]
  · rw [h 2931 (by omega)]
  · exact hr i σ σ' h

/-- **The honest oracle** on the memory `rd1`, at the arguments `args`. -/
noncomputable def vsW (rd1 : Reader) (args : List E) (cur p : ℕ) (ret : ℕ → (ℕ → E) → E) : ℕ → E :=
  fixW (vsΦ rd1 args) (vsRule cur p ret)

section
variable {rd1 : Reader} {args : List E} {cur p : ℕ} {ret : ℕ → (ℕ → E) → E}

/-- **The honest oracle's equation**: word `i` is the rule on `verify_sub`'s values at it. -/
theorem vsW_eq (ha : args.length = 6) (hr : CausalRule ret) (i : ℕ) :
    vsW rd1 args cur p ret i = vsRule cur p ret i fun j => vsVal rd1 (vsW rd1 args cur p ret) args (.n j) :=
  vsFix_eq ha (vsRule_causal hr) i

theorem vsAllocIdx_nodup : vsAllocIdx.Nodup := by decide

theorem vsW_alloc (ha : args.length = 6) (hr : CausalRule ret) {j : ℕ} (hj : j < 24) :
    vsW rd1 args cur p ret (vsAllocIdx.getD j 0) =
      ofK (addressOfIndex ((bases cur (vsAllocSz p)).getD j 0)) := by
  have hl : j < vsAllocIdx.length := hj
  have hm : vsAllocIdx.getD j 0 ∈ vsAllocIdx := by
    rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem hl
  rw [vsW_eq ha hr]
  simp only [vsRule, hm, ↓reduceIte]
  rw [List.getD_eq_getElem _ _ hl, vsAllocIdx_nodup.idxOf_getElem]

theorem vsW_42 (ha : args.length = 6) (hr : CausalRule ret) : vsW rd1 args cur p ret 42 = gen ^ p := by
  rw [vsW_eq ha hr]
  simp [vsRule, vsAllocIdx]

/-- A word outside the rule's own groups is `ret`'s. -/
theorem vsW_ret (ha : args.length = 6) (hr : CausalRule ret) {i : ℕ} (h1 : i ∉ vsAllocIdx) (h2 : i ≠ 42)
    (h3 : ¬(512 ≤ i ∧ i ≤ 516)) (h4 : ¬(581 ≤ i ∧ i ≤ 586)) (h5 : ¬(2943 ≤ i ∧ i ≤ 2947)) :
    vsW rd1 args cur p ret i = ret i fun j => vsVal rd1 (vsW rd1 args cur p ret) args (.n j) := by
  rw [vsW_eq ha hr]
  simp only [vsRule, h1, h2, h3, h4, h5, ↓reduceIte]

end

end
end LeanVM.Guest.B1.VsC
