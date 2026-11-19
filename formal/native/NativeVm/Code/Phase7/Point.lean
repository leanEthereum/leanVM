module

public import NativeVm.Code.Phase7.Preds
public import NativeVm.Code.Phase7.EOps
public import NativeVm.Transcript.QueryPre

/-!
# The final level's points

`pointC` writes the final level's point `α's ++ tail` at `ptO` (WHIR's `α`s from `whirR`, the
sumcheck's challenges from `spO`, their count at `cMu`) and its rotation by six coordinates,
`point[6..] ++ point[..6]`, at `xO`, the point the basis is evaluated at. Four word copies
(`cpy`, `rcx` words from `rsi` to `rdx`, from the last).
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model LeanVM.Parameters
open NativeVm.Transcript (wd Fits Disj Env wdisp ctxWork wd_inj wd_zero wp_load wp_store wp_reg
  toNat_toUInt64)

namespace PT

/-! ## Elements as words -/

/-- Word `j` of the elements `xs`, two words an element, limb `0` first. -/
def ewWord (xs : Array EW) (j : Nat) : UInt64 :=
  if j % 2 = 0 then (xs.getD (j / 2) 0).c0 else (xs.getD (j / 2) 0).c1

theorem ewArr_words {m : UInt64 → Option UInt64} {p : UInt64} {xs : Array EW} (h : EWArr m p xs) :
    ∀ j < 2 * xs.size, m (wd p j) = some (ewWord xs j) := fun j hj ↦ by
  have hi : j / 2 < xs.size := by omega
  obtain ⟨h0, h1⟩ := h (j / 2) hi
  rw [wd_wd] at h1
  have g : xs.getD (j / 2) 0 = xs[j / 2] := (Array.getElem_eq_getD (h := hi) 0).symm
  unfold ewWord
  rcases Nat.mod_two_eq_zero_or_one j with e | e
  · simp only [e, ↓reduceIte, g]
    rw [show 2 * (j / 2) = j by omega] at h0
    exact h0
  · simp only [e, one_ne_zero, ↓reduceIte, g]
    rw [show 2 * (j / 2) + 1 = j by omega] at h1
    exact h1

theorem ewArr_of_words {m : UInt64 → Option UInt64} {p : UInt64} {xs : Array EW}
    (h : ∀ j < 2 * xs.size, m (wd p j) = some (ewWord xs j)) : EWArr m p xs := fun i hi ↦ by
  have h0 := h (2 * i) (by omega)
  have h1 := h (2 * i + 1) (by omega)
  refine ⟨?_, ?_⟩
  · rw [h0, ewWord, show 2 * i / 2 = i by omega, Array.getElem_eq_getD 0]
    simp
  · rw [wd_wd, h1, ewWord, show (2 * i + 1) / 2 = i by omega, Array.getElem_eq_getD 0]
    simp

theorem ewWord_congr {xs ys : Array EW} {j k : Nat} (hp : j % 2 = k % 2)
    (h : xs.getD (j / 2) 0 = ys.getD (k / 2) 0) : ewWord xs j = ewWord ys k := by
  unfold ewWord
  rw [h, hp]

/-! ## Steps -/

variable {env : Env} {s : QState} {P E : QState → Prop} {rest : List Stmt}

/-- `base + 8 · index + 8 k`. -/
def ix (b i : Reg64) (k : Nat) : Addr := { base := b, idx := some (i, .W64), disp := wdisp k }

theorem ldW_wp (hrdi : s.reg .rdi = env.ctx) (hwp : s.mem (wd env.ctx ctxWork) = some env.work)
    (h : WP (blk rest) (s.setReg .rbp env.work) P E) : WP (blk (ldW :: rest)) s P E :=
  wp_load (NativeVm.Transcript.eval_cw hrdi ctxWork) hwp h

theorem leaw_wp {d : Reg64} {k : Nat} (hW : s.reg .rbp = env.work)
    (h : WP (blk rest) (s.setReg d (wd env.work k)) P E) : WP (blk (leaw d k :: rest)) s P E :=
  wp_reg (i := .lea d (at_ .rbp (wdisp k))) (by rw [QInstr.step, eval_w hW k]) h

theorem shl_eq (n k : Nat) (hk : k < 64) : n.toUInt64 <<< (k.toUInt64) = (2 ^ k * n).toUInt64 :=
  NativeVm.Transcript.toUInt64_shl n k hk

theorem shl1 (n : Nat) : n.toUInt64 <<< (1 : UInt64) = (2 * n).toUInt64 := by
  have h := shl_eq n 1 (by norm_num); rwa [show (2 : Nat) ^ 1 = 2 by norm_num] at h

theorem shl4 (n : Nat) : n.toUInt64 <<< (4 : UInt64) = (8 * (2 * n)).toUInt64 := by
  have h := shl_eq n 4 (by norm_num)
  rwa [show (2 : Nat) ^ 4 * n = 8 * (2 * n) by ring] at h

theorem succ_sub1 (n : Nat) : (n + 1).toUInt64 - 1 = n.toUInt64 := by
  rw [Nat.toUInt64_eq, Nat.toUInt64_eq, UInt64.ofNat_add]
  simp

theorem sub6 {n : Nat} (hn : 6 ≤ n) (h : n < 2 ^ 64) : n.toUInt64 - 6 = (n - 6).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le, toNat_toUInt64 h]; exact hn), toNat_toUInt64 h,
    toNat_toUInt64 (by omega)]
  rfl

/-! ## The copy -/

/-- `rcx` words from `rsi` to `rdx`, from the last. -/
def cpy : Stmt := .loop (.test false .rcx (.reg .rcx)) (blk [
  I (.subi .rcx 1), I (.load .rax (ix .rsi .rcx 0)), I (.store (ix .rdx .rcx 0) .rax)])

theorem cpy_spec {t : QState} {F : QState → Prop} {S D : UInt64} {c : Nat} {f : Nat → UInt64}
    (hsi : t.reg .rsi = S) (hdx : t.reg .rdx = D) (hcx : t.reg .rcx = c.toUInt64)
    (hc : c < 2 ^ 61) (hS : ∀ j < c, t.mem (wd S j) = some (f j))
    (hD : ∀ j < c, (t.mem (wd D j)).isSome) (hsep : ∀ j < c, ∀ k < c, wd D j ≠ wd S k) :
    WP cpy t (fun t' ↦ (∀ j < c, t'.mem (wd D j) = some (f j)) ∧
      (∀ a, (∀ j < c, a ≠ wd D j) → t'.mem a = t.mem a) ∧
      (∀ a, (t'.mem a).isSome = (t.mem a).isSome) ∧ RegsFrame [.rax, .rcx] t t') F := by
  unfold cpy
  apply WP.loop (fun t' ↦ ∃ k ≤ c, t'.reg .rcx = k.toUInt64 ∧
      (∀ j, k ≤ j → j < c → t'.mem (wd D j) = some (f j)) ∧
      (∀ a, (∀ j < c, a ≠ wd D j) → t'.mem a = t.mem a) ∧
      (∀ a, (t'.mem a).isSome = (t.mem a).isSome) ∧ RegsFrame [.rax, .rcx] t t')
    (fun t' ↦ (t'.reg .rcx).toNat)
  · exact ⟨c, le_rfl, hcx, fun j hj hjc ↦ absurd hjc (by omega), fun _ _ ↦ rfl, fun _ ↦ rfl,
      Field.RegsFrame.refl _ _⟩
  · intro t' ⟨k, hk, hk', hW, hF, hd, hf⟩ hcnd
    have hk0 : k ≠ 0 := fun e ↦ by
      have : t'.reg .rcx ≠ 0 := by simpa [Cond.eval, Rhs.eval] using hcnd
      exact this (by rw [hk', e]; rfl)
    have hcx1 : t'.reg .rcx - 1 = (k - 1).toUInt64 := by
      rw [hk', show k = k - 1 + 1 by omega, succ_sub1, Nat.add_sub_cancel]
    have rs' : t'.reg .rsi = S := by rw [hf .rsi (by decide)]; exact hsi
    have rd' : t'.reg .rdx = D := by rw [hf .rdx (by decide)]; exact hdx
    fstep
    refine wp_load (NativeVm.Transcript.eval_idx64 (j := 0) (b := S) (i := k - 1)
      (by rsimp; rw [rs', wd_zero]) (by rsimp; exact hcx1) 0) (v := f (k - 1)) ?_ ?_
    · rsimp
      rw [show 0 + (k - 1) + 0 = k - 1 by omega,
        hF _ fun j hj ↦ (hsep j hj (k - 1) (by omega)).symm]
      exact hS _ (by omega)
    refine wp_store (NativeVm.Transcript.eval_idx64 (j := 0) (b := D) (i := k - 1)
      (by rsimp; rw [rd', wd_zero]) (by rsimp; exact hcx1) 0) ?_ ?_
    · rsimp; rw [show 0 + (k - 1) + 0 = k - 1 by omega, hd]; exact hD _ (by omega)
    apply WP.blk_nil
    rw [show 0 + (k - 1) + 0 = k - 1 by omega]
    refine ⟨⟨k - 1, by omega, by rsimp; exact hcx1, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro j hj hjc
      simp only [QState.setMem_mem, QState.setReg_mem, QState.setReg_reg, ↓reduceIte]
      by_cases e : j = k - 1
      · subst e; simp
      · have ne : wd D j ≠ wd D (k - 1) := fun h ↦ e ((wd_inj (by omega) (by omega)).mp h)
        simp only [ne, ite_false]
        exact hW j (by omega) hjc
    · intro a ha
      simp only [QState.setMem_mem, QState.setReg_mem, ha (k - 1) (by omega), ite_false]
      exact hF a ha
    · intro a
      simp only [QState.setMem_mem, QState.setReg_mem]
      split
      · rename_i e; subst e; simp only [Option.isSome_some]; exact (hD (k - 1) (by omega)).symm
      · exact hd a
    · intro q hq
      have hq' := hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq'
      simp only [QState.setMem_reg, QState.setReg_reg, hq'.1, hq'.2, ↓reduceIte]
      exact hf q hq
    · rsimp
      rw [hcx1, hk', toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
      omega
  · intro t' ⟨k, hk, hk', hW, hF, hd, hf⟩ hcnd
    have hk0 : k = 0 := by
      have : t'.reg .rcx = 0 := by simpa [Cond.eval, Rhs.eval] using hcnd
      rw [hk'] at this
      exact (NativeVm.Transcript.toUInt64_inj (b := 0) (by omega) (by norm_num)).mp this
    subst hk0
    exact ⟨fun j hj ↦ hW j (Nat.zero_le _) hj, hF, hd, hf⟩

/-- `cpy` between two runs of the working area's words. -/
theorem cpy_w {t : QState} {Q F : QState → Prop} {o d c : Nat} {f : Nat → UInt64}
    (hsi : t.reg .rsi = wd env.work o) (hdx : t.reg .rdx = wd env.work d)
    (hcx : t.reg .rcx = c.toUInt64) (hS : ∀ j < c, t.mem (wd env.work (o + j)) = some (f j))
    (hd : ∀ j < c, (t.mem (wd env.work (d + j))).isSome) (hsep : o + c ≤ d ∨ d + c ≤ o)
    (hb : o + c < 2 ^ 61) (hb' : d + c < 2 ^ 61)
    (h : ∀ t' : QState, (∀ j < c, t'.mem (wd env.work (d + j)) = some (f j)) →
      (∀ a, (∀ j < c, a ≠ wd env.work (d + j)) → t'.mem a = t.mem a) →
      (∀ a, (t'.mem a).isSome = (t.mem a).isSome) → RegsFrame [.rax, .rcx] t t' →
      WP (blk rest) t' Q F) :
    WP (blk (cpy :: rest)) t Q F :=
  Field.WP.then (cpy_spec (S := wd env.work o) (D := wd env.work d) (f := f) hsi hdx hcx
    (by omega) (fun j hj ↦ by rw [wd_wd]; exact hS j hj) (fun j hj ↦ by rw [wd_wd]; exact hd j hj)
    (fun j hj k hk ↦ by rw [wd_wd, wd_wd]; exact wd_ne (by omega) (by omega) (by omega)))
    fun t' ⟨h1, h2, h3, h4⟩ ↦ h t' (fun j hj ↦ by rw [← wd_wd]; exact h1 j hj)
      (fun a ha ↦ h2 a fun j hj ↦ by rw [wd_wd]; exact ha j hj) h3 h4

/-! ## The points' words -/

theorem getD_append_left {xs ys : Array EW} {i : Nat} (h : i < xs.size) :
    (xs ++ ys).getD i 0 = xs.getD i 0 := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_append_left h]

theorem getD_append_right {xs ys : Array EW} {i : Nat} :
    (xs ++ ys).getD (xs.size + i) 0 = ys.getD i 0 := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_append_right]

theorem ewWord_left {xs ys : Array EW} {j : Nat} (h : j < 2 * xs.size) :
    ewWord (xs ++ ys) j = ewWord xs j :=
  ewWord_congr rfl (getD_append_left (by omega))

theorem ewWord_right {xs ys : Array EW} (j : Nat) :
    ewWord (xs ++ ys) (2 * xs.size + j) = ewWord ys j :=
  ewWord_congr (by omega) (by rw [show (2 * xs.size + j) / 2 = xs.size + j / 2 by omega,
    getD_append_right])

theorem getD_extract {xs : Array EW} {a b i : Nat} (h : a + i < b) (hb : b ≤ xs.size) :
    (xs.extract a b).getD i 0 = xs.getD (a + i) 0 := by
  simp [Array.getD_eq_getD_getElem?, show i < min b xs.size - a by omega,
    show a + i < xs.size by omega]

/-- The rotation's words: the point's words from `12`, then its first `12`. -/
theorem ewWord_rot {P : Array EW} (h6 : 6 ≤ P.size) {j : Nat} (hj : j < 2 * P.size) :
    ewWord (P.extract 6 P.size ++ P.extract 0 6) j =
      if j < 2 * (P.size - 6) then ewWord P (12 + j) else ewWord P (j - 2 * (P.size - 6)) := by
  have hs : (P.extract 6 P.size).size = P.size - 6 := by simp
  split
  · rw [ewWord_left (by rw [hs]; omega)]
    exact ewWord_congr (by omega) (by
      rw [getD_extract (by omega) le_rfl, show (12 + j) / 2 = 6 + j / 2 by omega])
  · have e := ewWord_right (xs := P.extract 6 P.size) (ys := P.extract 0 6) (j - 2 * (P.size - 6))
    rw [hs, show 2 * (P.size - 6) + (j - 2 * (P.size - 6)) = j by omega] at e
    rw [e]
    exact ewWord_congr rfl (by rw [getD_extract (by omega) h6, Nat.zero_add])

end PT

open PT

/-- Unfold the scratch offsets, then `omega`. -/
macro "pomega" : tactic => `(tactic| (
  simp only [ptO, xO, spO, cMu, sc, scratch_off, whir_off, mineLo_val, dataEnd_val] at *
  omega))

/-- **The final level's points**: `α's ++ tail` at `ptO`, its rotation by six at `xO`. -/
def pointC : Stmt := blk [
  ldW,
  ldw .rcx (whirR.off + 2), I (.shli .rcx 1), leaw .rsi (whirR.off + 3), leaw .rdx ptO, cpy,
  ldw .rcx cMu, I (.shli .rcx 1), leaw .rsi spO, ldw .rax (whirR.off + 2), I (.shli .rax 4),
  leaw .rdx ptO, I (.add .rdx .rax), cpy,
  ldw .rcx (whirR.off + 2), ldw .rax cMu, I (.add .rcx .rax), I (.subi .rcx 6),
  I (.mov .rbx .rcx), I (.shli .rcx 1), leaw .rsi (ptO + 12), leaw .rdx xO, cpy,
  I (.movi .rcx 12), leaw .rsi ptO, I (.shli .rbx 4), leaw .rdx xO, I (.add .rdx .rbx), cpy]

theorem pointC_spec {p : Par} {s : QState} {F : QState → Prop} {sW : WhirStateW}
    {tail : Array EW}
    (hrdi : s.reg .rdi = p.env.ctx) (hin : Inputs p.env p.inp s.mem)
    (hwp : s.mem (wd p.env.ctx ctxWork) = some p.env.work)
    (hW : WhirAt s.mem (whirR.at p.env.work) sW) (ht : EWArr s.mem (wd p.env.work spO) tail)
    (htn : NatAt s.mem (wd p.env.work cMu) tail.size)
    (h30 : sW.alphas.size + tail.size ≤ 30) (h6 : 6 ≤ sW.alphas.size + tail.size) :
    WP pointC s (fun s' ↦ EWArr s'.mem (wd p.env.work ptO) (sW.alphas ++ tail) ∧
      EWArr s'.mem (wd p.env.work xO) ((sW.alphas ++ tail).extract 6 (sW.alphas ++ tail).size ++
        (sW.alphas ++ tail).extract 0 6) ∧
      FrM p.env s s' ∧
      Only p.env (fun j ↦ ptO ≤ j ∧ j < ptO + 64 ∨ xO ≤ j ∧ j < xO + 64 ∨ sc 5 ≤ j ∧ j < sc 8)
        s.mem s'.mem) F := by
  set P := sW.alphas ++ tail with hP
  have hPs : P.size = sW.alphas.size + tail.size := Array.size_append
  have hN := workWords_ge p.inp.bytecode.size
  have hsome : ∀ k < 85438, (s.mem (wd p.env.work k)).isSome := fun k hk ↦ hin.workSome k (by omega)
  obtain ⟨-, hAv, -, -, -⟩ := hW
  obtain ⟨-, hAn, hAw⟩ := hAv
  simp only [Region.at, wd_wd] at hAn hAw
  rw [show whirR.off + 2 + 1 = whirR.off + 3 from rfl] at hAw
  have hAw' := ewArr_words hAw
  have htw := ewArr_words ht
  have hAs : sW.alphas.size ≤ 30 := by omega
  -- the words written
  let Wp : Nat → Prop := fun k ↦ ptO ≤ k ∧ k < ptO + 64 ∨ xO ≤ k ∧ k < xO + 64
  unfold pointC
  refine ldW_wp hrdi hwp ?_
  -- the α's
  refine ldw_wp (env := p.env) (by rsimp) (by rsimp; exact hAn.2) ?_
  fstep [shl1]
  refine leaw_wp (env := p.env) (by rsimp) ?_
  refine leaw_wp (env := p.env) (by rsimp) ?_
  refine cpy_w (env := p.env) (o := whirR.off + 3) (d := ptO) (c := 2 * sW.alphas.size) (f := ewWord sW.alphas) (by rsimp)
    (by rsimp) (by rsimp) (fun j hj ↦ by rsimp; rw [← wd_wd]; exact hAw' j hj)
    (fun j hj ↦ by rsimp; exact hsome _ (by pomega)) (by pomega) (by pomega) (by pomega)
    fun t₁ c1 f1 d1 r1 ↦ ?_
  rsimp at f1 d1
  have b1 : t₁.reg .rbp = p.env.work := by rw [r1 .rbp (by decide)]; rsimp
  have i1 : t₁.reg .rdi = p.env.ctx := by rw [r1 .rdi (by decide)]; rsimp; exact hrdi
  have m1 : ∀ k, (k < ptO ∨ ptO + 2 * sW.alphas.size ≤ k) → k < 2 ^ 61 →
      t₁.mem (wd p.env.work k) = s.mem (wd p.env.work k) :=
    fun k hk hk' ↦ f1 _ fun j hj ↦ wd_ne (by omega) hk' (by pomega)
  -- the tail
  refine ldw_wp (env := p.env) b1 (by rw [m1 _ (by pomega) (by pomega)]; exact htn.2) ?_
  fstep [shl1]
  refine leaw_wp (env := p.env) (by rsimp; exact b1) ?_
  refine ldw_wp (env := p.env) (by rsimp; exact b1)
    (by rsimp; rw [m1 _ (by pomega) (by pomega)]; exact hAn.2) ?_
  fstep [shl4]
  refine leaw_wp (env := p.env) (by rsimp; exact b1) ?_
  fstep [NativeVm.Transcript.wd_add]
  refine cpy_w (env := p.env) (o := spO) (d := ptO + 2 * sW.alphas.size) (c := 2 * tail.size) (f := ewWord tail)
    (by rsimp) (by rsimp) (by rsimp)
    (fun j hj ↦ by rsimp; rw [m1 _ (by pomega) (by pomega), ← wd_wd]; exact htw j hj)
    (fun j hj ↦ by rsimp; rw [d1]; exact hsome _ (by pomega)) (by pomega) (by pomega) (by pomega)
    fun t₂ c2 f2 d2 r2 ↦ ?_
  rsimp at f2 d2
  have b2 : t₂.reg .rbp = p.env.work := by rw [r2 .rbp (by decide)]; rsimp; exact b1
  have i2 : t₂.reg .rdi = p.env.ctx := by rw [r2 .rdi (by decide)]; rsimp; exact i1
  have pt2 : ∀ j < 2 * P.size, t₂.mem (wd p.env.work (ptO + j)) = some (ewWord P j) := by
    intro j hj
    by_cases hja : j < 2 * sW.alphas.size
    · rw [f2 _ fun i hi ↦ wd_ne (by pomega) (by pomega) (by pomega), c1 j hja, hP,
        ewWord_left hja]
    · have := c2 (j - 2 * sW.alphas.size) (by rw [hPs] at hj; omega)
      rw [show ptO + 2 * sW.alphas.size + (j - 2 * sW.alphas.size) = ptO + j by omega] at this
      rw [this, hP, ← ewWord_right (xs := sW.alphas) (ys := tail), show 2 * sW.alphas.size + (j - 2 * sW.alphas.size) = j by
        omega]
  have m2 : ∀ k, (k < ptO ∨ ptO + 64 ≤ k) → k < 2 ^ 61 →
      t₂.mem (wd p.env.work k) = s.mem (wd p.env.work k) :=
    fun k hk hk' ↦ by
      rw [f2 _ fun j hj ↦ wd_ne (by omega) hk' (by pomega)]
      exact m1 k (by omega) hk'
  -- the rotation
  have hn6 : (sW.alphas.size + tail.size).toUInt64 - 6 = (sW.alphas.size + tail.size - 6).toUInt64 :=
    sub6 h6 (by omega)
  refine ldw_wp (env := p.env) b2 (by rw [m2 _ (by pomega) (by pomega)]; exact hAn.2) ?_
  refine ldw_wp (env := p.env) (by rsimp; exact b2)
    (by rsimp; rw [m2 _ (by pomega) (by pomega)]; exact htn.2) ?_
  fstep [NativeVm.Transcript.toUInt64_add]
  fstep [hn6]
  fstep
  fstep [shl1]
  refine leaw_wp (env := p.env) (by rsimp; exact b2) ?_
  refine leaw_wp (env := p.env) (by rsimp; exact b2) ?_
  refine cpy_w (env := p.env) (o := ptO + 12) (d := xO) (c := 2 * (sW.alphas.size + tail.size - 6))
    (f := fun j ↦ ewWord P (12 + j)) (by rsimp) (by rsimp) (by rsimp)
    (fun j hj ↦ by rsimp; rw [Nat.add_assoc]; exact pt2 _ (by rw [hPs]; omega))
    (fun j hj ↦ by rsimp; rw [d2, d1]; exact hsome _ (by pomega)) (by pomega) (by pomega)
    (by pomega) fun t₃ c3 f3 d3 r3 ↦ ?_
  rsimp at f3 d3
  have b3 : t₃.reg .rbp = p.env.work := by rw [r3 .rbp (by decide)]; rsimp; exact b2
  have i3 : t₃.reg .rdi = p.env.ctx := by rw [r3 .rdi (by decide)]; rsimp; exact i2
  have x3 : t₃.reg .rbx = (sW.alphas.size + tail.size - 6).toUInt64 := by
    rw [r3 .rbx (by decide)]; rsimp
  fstep
  refine leaw_wp (env := p.env) (by rsimp; exact b3) ?_
  fstep [x3, shl4]
  refine leaw_wp (env := p.env) (by rsimp; exact b3) ?_
  fstep [NativeVm.Transcript.wd_add]
  refine cpy_w (env := p.env) (o := ptO) (d := xO + 2 * (sW.alphas.size + tail.size - 6)) (c := 12) (f := ewWord P)
    (by rsimp) (by rsimp) (by rsimp)
    (fun j hj ↦ by
      rsimp; rw [f3 _ fun i hi ↦ wd_ne (by pomega) (by pomega) (by pomega)]
      exact pt2 _ (by rw [hPs]; omega))
    (fun j hj ↦ by rsimp; rw [d3, d2, d1]; exact hsome _ (by pomega)) (by pomega) (by pomega)
    (by pomega) fun t₄ c4 f4 d4 r4 ↦ ?_
  rsimp at f4 d4
  apply WP.blk_nil
  have m4 : ∀ a, (∀ k, Wp k → a ≠ wd p.env.work k) → t₄.mem a = s.mem a := fun a ha ↦ by
    rw [f4 a fun j hj ↦ ha _ (.inr ⟨by omega, by pomega⟩),
      f3 a fun j hj ↦ ha _ (.inr ⟨by omega, by pomega⟩),
      f2 a fun j hj ↦ ha _ (.inl ⟨by omega, by pomega⟩),
      f1 a fun j hj ↦ ha _ (.inl ⟨by omega, by pomega⟩)]
  have dm : ∀ a, (t₄.mem a).isSome = (s.mem a).isSome := fun a ↦ by rw [d4, d3, d2, d1]
  refine ⟨ewArr_of_words fun j hj ↦ ?_, ewArr_of_words fun j hj ↦ ?_, ?_, ?_⟩
  · rw [wd_wd, f4 _ fun i hi ↦ wd_ne (by pomega) (by pomega) (by pomega),
      f3 _ fun i hi ↦ wd_ne (by pomega) (by pomega) (by pomega)]
    exact pt2 j hj
  · rw [wd_wd]
    have hXs : (P.extract 6 P.size ++ P.extract 0 6).size = P.size := by
      simp; omega
    rw [hXs] at hj
    rw [ewWord_rot (by omega) hj]
    split
    · rw [f4 _ fun i hi ↦ wd_ne (by pomega) (by pomega) (by pomega)]
      exact c3 j (by rw [hPs] at *; omega)
    · have := c4 (j - 2 * (sW.alphas.size + tail.size - 6)) (by rw [hPs] at hj; omega)
      rw [show xO + 2 * (sW.alphas.size + tail.size - 6) + (j - 2 * (sW.alphas.size + tail.size - 6)) = xO + j by
        rw [hPs] at hj; omega] at this
      rw [this, hPs]
  · exact ⟨by rw [r4 .rdi (by decide)]; rsimp; exact i3.trans hrdi.symm, dm, fun a ha ↦ m4 a
      fun k hk e ↦ ha ⟨k, by rcases hk with h | h <;> pomega, by rcases hk with h | h <;> pomega, e⟩⟩
  · intro k h1 h2 hk
    exact m4 _ fun k' hk' e ↦ hk (by
      have := (wd_inj (by pomega) (by rcases hk' with h | h <;> pomega)).mp e
      subst this; rcases hk' with h | h
      · exact .inl h
      · exact .inr (.inl h))

end NativeVm.Code.P7
