/-
  LeanVM.Guest.EndExecRCs

  `column_selector`'s lowest digit (F3), sound at the honest frames given its offset's alignment
  and the nibble shares at `sel_g` (`CsQ`).
-/

module

public import LeanVM.Guest.EndExecRE
public import LeanVM.Guest.Res.MonoChain

/-!
# `column_selector`'s lowest digit

`CsQ r J`: at an instance of `column_selector__L{κ}`, its offset is `g^o`, `o < 2^32` a multiple of
`2^κ`, and `sel_g` holds the nibble shares (`GTabsAt`), as `check_opening_terminal`'s dispatch hands
them.

`cs_digit`: on such arguments, the digits' range checks and `rebuilt = offset` make the offset's
exponent `16^(κ/4)` times the digits' number (`csDig`), so the lowest digit `g^u`, `u < 16`, is a
multiple of `2^(4 - w)` (`B1.Tables.cs_dvd`), `w` its width. `cs_top` (F3): at an honest frame
with `CsQ`, the digit's cell holds it, so the read at `[s]·g^u·g^off` is the strided table's entry
`u / 2^(4 - w) < 2^w`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf entryOf FrameHolds fsN fn_of_idx cellJ namedOf)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (csRes csKappa csB inFr topAtoms)
open LeanVM.Guest.B1.Tables (csPre csNibT csN csW csC csRb csHint csDig holds_csNib cs_dvd csDig_lt
  prod_gen_pow_csDig csNibT_noRet csPre_noRet csFound csRet csW_bounds GTabsAt lName)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

@[expose] public section

/-- `column_selector__L{κ}`'s arguments as its caller hands them: the offset `g^o`, `o < 2^32` a
multiple of `2^κ`, and the nibble shares at `sel_g`. -/
def CsH (rd : Reader) (κ : ℕ) : List E → Prop
  | [off, _se, sg] => ∃ o < 2 ^ 32, 2 ^ κ ∣ o ∧ off = gen ^ o ∧ GTabsAt rd sg
  | _ => False

/-- **`column_selector`'s arguments at its instances.** -/
def CsQ (r : Ref) (J : Inst) : Prop :=
  ∀ f σ bufs kids, J.t = .node f σ bufs kids → ∀ κ < 31, f = lName "column_selector" κ → ∀ fn,
    coreProgram.find? f = some fn → CsH r.img.read κ (fn.params.map σ)

end

public section

/-- **The lowest digit**: `g^u`, `u < 16`, a multiple of `2^(3 - (w - 1))`, once the offset is
aligned. -/
theorem cs_digit {κ : ℕ} (hκ : κ < 31) {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ) {C : CallRel}
    {σ : Core.Val} {kret : List E → Prop} (hpre : Stmt.HoldsList C Lm.read σ (csPre κ) True kret)
    (hG : GTabsAt Lm.read (σ (.n 2))) {o : ℕ} (ho : o < 2 ^ 32) (hal : 2 ^ κ ∣ o)
    (h0 : σ (.n 0) = gen ^ o) : ∃ u < 16, σ (.n 3) = gen ^ u ∧ 2 ^ (3 - (csW κ 0 - 1)) ∣ u := by
  have h32 : κ ≠ 32 := by omega
  simp only [csPre, h32, ↓reduceIte, csHint, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and] at hpre
  rw [holdsList_append, holdsList_flatten _ (fun b hb => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hb; exact csNibT_noRet κ t)] at hpre
  obtain ⟨hnibs, htail⟩ := hpre
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at htail
  obtain ⟨hassert, -⟩ := htail
  set N := csN κ with hNdef
  set b := κ / 4 with hbdef
  have hN1 : 1 ≤ N := by simp only [hNdef, csN]; omega
  have hNb : b + N = 8 := by simp only [hNdef, hbdef, csN]; omega
  have hNib : ∀ k < N, _ := fun k hk => holds_csNib hμ Lm (C := C) (σ := σ) (kret := kret) (κ := κ) (k := k)
    (hnibs _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
  choose u hu hd xe xg hxe hxg hsel hrb using hNib
  let u' : ℕ → ℕ := fun k ↦ if hk : k < N then u k hk else 0
  have hu' : ∀ k < N, u' k < 16 := fun k hk => by simp only [u', hk, ↓reduceDIte]; exact hu k hk
  let xg' : ℕ → E := fun k ↦ if hk : k < N then xg k hk else 1
  have hR : ∀ k < N, σ (.n (csRb κ k)) = ∏ m ∈ Finset.range (k + 1), xg' m := by
    intro k hk
    induction k with
    | zero => rw [hrb 0 hk]; simp [xg', hk]
    | succ k ih =>
      rw [hrb (k + 1) hk, Finset.prod_range_succ]
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [ih (by omega)]; simp [xg', hk]
  have hxg' : ∀ k < N, xg' k = gen ^ (u' k * 16 ^ (b + k)) := by
    intro k hk
    have h1 := hG (b + k) (show b + k < 8 by omega) (u k hk) (hu k hk)
    have h2 := hxg k hk
    rw [show u k hk + 16 * (b + k) = 16 * (b + k) + u k hk by omega] at h2
    simp only [xg', u', hk, ↓reduceDIte]
    exact B1.Tables.tb_loadHolds_unique h2 h1
  have hreb : σ (.n 0) = gen ^ (16 ^ b * csDig u' N) := by
    have e0 := Value.e_add_eq_zero_iff.mp hassert
    rw [← e0, hR (N - 1) (by omega), show N - 1 + 1 = N by omega,
      Finset.prod_congr rfl (fun k hk => hxg' k (Finset.mem_range.mp hk)), prod_gen_pow_csDig]
  have hlt : 16 ^ b * csDig u' N < 2 ^ 32 := by
    have := csDig_lt hu'
    rw [show 16 ^ b = 2 ^ (4 * b) by rw [pow_mul]; norm_num]
    calc 2 ^ (4 * b) * csDig u' N < 2 ^ (4 * b) * 2 ^ (4 * N) :=
          Nat.mul_lt_mul_of_pos_left this (Nat.two_pow_pos _)
      _ = 2 ^ 32 := by rw [← pow_add, show 4 * b + 4 * N = 32 by omega]
  have hoe : o = 16 ^ b * csDig u' N :=
    Value.gen_pow_inj (by omega) (by omega) (h0.symm.trans hreb)
  have hdv := cs_dvd hu' (hoe ▸ hal) 0 (by omega)
  refine ⟨u 0 (by omega), hu 0 _, by simpa using hd 0 (by omega), ?_⟩
  simpa [u', show 0 < N by omega] using hdv

/-- The atoms of a block of atoms are top-level atoms of it and anything after it. -/
theorem mem_topAtoms_atoms : ∀ {l : List Stmt} (rest : List Stmt), (∀ s ∈ l, ∃ a, s = .atom a) →
    ∀ {a : Atom}, Stmt.atom a ∈ l → a ∈ topAtoms (l ++ rest)
  | [], _, _, _, h => by simp at h
  | s :: l, rest, hl, a, h => by
    obtain ⟨b, rfl⟩ := hl s List.mem_cons_self
    simp only [List.cons_append, topAtoms, List.mem_cons, Stmt.atom.injEq] at h ⊢
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (mem_topAtoms_atoms rest (fun s hs ↦ hl s (List.mem_cons_of_mem _ hs)) h)

theorem csNibT_atoms (κ k : ℕ) : ∀ s ∈ csNibT κ k, ∃ a, s = .atom a := by
  intro s hs
  unfold csNibT at hs
  split at hs
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with h | h | h | h | h | h <;> exact ⟨_, h⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with h | h | h | h | h | h | h | h <;> exact ⟨_, h⟩

theorem csPre_atoms {κ : ℕ} (h32 : κ ≠ 32) : ∀ s ∈ csPre κ, ∃ a, s = .atom a := by
  intro s hs
  simp only [csPre, h32, ↓reduceIte, List.mem_cons, List.mem_append, List.mem_flatten, List.mem_map,
    List.mem_range, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | (⟨_, ⟨k, -, rfl⟩, hs⟩ | rfl | rfl)
  · exact ⟨_, rfl⟩
  · exact csNibT_atoms κ k s hs
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem csW_sub {κ : ℕ} : 3 - (csW κ 0 - 1) = 4 - csW κ 0 := by
  have := csW_bounds κ 0; omega

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}

/-- **F3 at an honest frame**: the lowest digit's read lies in its strided table. -/
theorem cs_top (t : TopAt A r K i e j) (hr : r.Ok) (hC : CsQ r e.I) {x : Mode.Res} (hx : csB j x = true) :
    RRes (refMem r.img) e.I.fp x := by
  have hκ28 : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  match x, hx with
  | .sub a [b], hx =>
    simp only [csB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hx
    obtain ⟨⟨⟨hκ, hname⟩, hdin⟩, hxe⟩ := hx
    set κ := csKappa a.q.k with hκdef
    obtain ⟨f, bufs, kids, hJ, hf, hfn⟩ := t.found
    rw [hfn] at hname
    obtain ⟨fn, hfc, hps, hbody⟩ := csFound hκ
    rw [← hname] at hfc
    obtain rfl : coreOf j = fn := Option.some.inj (hf.symm.trans hfc)
    -- the caller's facts
    have hH := hC f e.σ bufs kids hJ κ hκ hname _ hf
    rw [hps] at hH
    obtain ⟨o, ho, hal, h0, hG⟩ := hH
    -- the body at the instance's valuation
    obtain ⟨args, rets, hv⟩ := inst_valid' hr t.inst hJ
    have hfs : ∀ f', 1 ≤ B2C.fs f' := fun f' ↦ by
      unfold B2C.fs; split <;> simp [B2C.mainFrame, Data.mainCells, Data.jtSlots]
    obtain ⟨-, hb⟩ := Res.holds_of_valid hfs hv hf
    rw [hbody, holdsList_append, holdsList_noRet _ (csPre_noRet κ)] at hb
    obtain ⟨u, hu, hd, hdv⟩ := cs_digit hκ (by omega) r.img hb.1 hG ho hal h0
    rw [csW_sub] at hdv
    -- the digit's cell
    obtain ⟨vs, hw, hF, -⟩ := t.events hr
    have hon : Ev.atom (.rangeCheck (.n 3) (.n (csC κ 0 + 1)) (.n (csC κ 0 + 2)) (.n (csC κ 0 + 3))
        (.n (csC κ 0))) ∈ e.pre ++ e.es := by
      refine topAtoms_on_path hw ?_
      rw [hbody]
      refine mem_topAtoms_atoms _ (csPre_atoms (by omega)) ?_
      simp only [csPre, show κ ≠ 32 by omega, ↓reduceIte, List.mem_cons, List.mem_append, List.mem_flatten,
        List.mem_map, List.mem_range]
      refine Or.inr (Or.inl ⟨csNibT κ 0, ⟨0, by simp only [csN]; omega, rfl⟩, ?_⟩)
      simp [csNibT]
    simp only [inFr, Bool.and_eq_true, decide_eq_true_eq] at hdin
    have hdc := t.cell hr hF (namedOf_atom hon (by simp [atomUses])) hdin.1 hdin.2
    rw [hd] at hdc
    -- the run
    rw [hxe]
    set w := csW κ 0 with hw'
    have hw4 := csW_bounds κ 0
    obtain ⟨q, rfl⟩ := hdv
    have hS : 0 < 2 ^ (4 - w) := Nat.two_pow_pos _
    have hq : q < 2 ^ w := by
      have h16 : 2 ^ (4 - w) * 2 ^ w = 16 := by rw [← pow_add, show 4 - w + w = 4 by omega]; rfl
      by_contra hc
      have := Nat.mul_le_mul_left (2 ^ (4 - w)) (not_lt.mp hc)
      omega
    refine ⟨0, 1, rfl, rfl, fun vq hvq jj _ hjj ↦ ⟨_, List.mem_singleton_self _, fun vb ylo yhi hvb hlo hhi ↦ ?_⟩⟩
    obtain rfl : jj = 0 := by omega
    change ylo = 0 at hlo
    change yhi = 2 ^ w at hhi
    refine ⟨q, by omega, by omega, ?_⟩
    obtain ⟨wq, hwq, rfl⟩ := hvq
    obtain ⟨wb, hwb, rfl⟩ := hvb
    obtain ⟨ud, wl, hud, hwl, rfl⟩ := rbs_insert_inv hwq
    rw [rbs_uniq hwl hwb]
    change refMem r.img (e.I.fp + cellJ j (.n 3)) = ud at hud
    rw [← hud, hdc]
    simp only [pow_zero, one_mul, mul_zero, zero_add, pow_one, ofK_gpow]
    rw [pow_add]
    ring
  | .sub _ [], hx => simp [csB] at hx
  | .sub _ (_ :: _ :: _), hx => simp [csB] at hx
  | .lt _ _, hx => simp [csB] at hx
  | .nz _, hx => simp [csB] at hx
  | .name _, hx => simp [csB] at hx

end

end

end LeanVM.Guest.EndExec
