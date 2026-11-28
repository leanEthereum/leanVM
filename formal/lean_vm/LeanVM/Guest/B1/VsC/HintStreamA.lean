/-
  LeanVM.Guest.B1.VsC.HintStreamA

  `hint_stream` completes placed, popping the stream's chunks.
-/

module

public import LeanVM.Guest.B1.VsC.HintStreamC
public import LeanVM.Guest.Complete.ComposeL
public import LeanVM.Guest.Complete.MainA
public import LeanVM.Guest.Memory.LowDef
import LeanVM.Guest.CoreRef

/-!
# `hint_stream`, placed

`hint_stream_complete` is layout-free. Placed, `hint_stream` and its loop own no words, place no
`HeapBuf` and no `frameAddr`; the loop's heap witness writes the stream's chunk `i` at
`stream·g^(256 i)`, so its hints lie in the region the caller hands it (the stream's `256 n`
cells). The loop's frames chain at `fp + fs loop` (`callAtA_nodeL`), its block `hsB fs (n - i)`
from iteration `i`, every frame ending at the cursor; the main body by `callAtA_node`, the loop
at the aligned base of its cursor. `hint_stream_completeA`: at every frame `fp` and cursor `c`
past it, on the stream's cells at `ptrAt s`, the call completes placed, ending at
`allocBase (al loop) c + hsB fs n`, popping the chunks in order, every node exact.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Protocol.Verifier LeanVM.Guest.Value
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- The block of the loop's frames from `m` iterations before its end: `m` frames, then the tail. -/
def hsB (fs : String → ℕ) : ℕ → ℕ
  | 0 => fs (tailKey hsLoopName)
  | m + 1 => fs hsLoopName + hsB fs m

/-- Iteration `i`'s events hold on every memory. -/
theorem hs_events (i n : ℕ) (stream : E) (rd : Reader) :
    ∀ e ∈ hsLoopPre.flatMap (slEvs (hsσ i n stream)), e.Holds rd (hsσ i n stream) := by
  set σ := hsσ i n stream with hσ
  have v : ∀ j, σ (.n j) = (hsVals i n stream).getD j 0 := fun _ => rfl
  intro e he
  rw [List.mem_flatMap] at he
  obtain ⟨s, hs, he⟩ := he
  simp only [hsLoopPre, List.mem_append, List.mem_map, List.mem_singleton] at hs
  rcases hs with ⟨a, ha, rfl⟩ | rfl
  · simp only [slEvs, List.mem_singleton] at he
    subst he
    simp only [hsLoopAtoms, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Ev.Holds, Atom.Holds, v, hsVals, List.getD_cons_succ, List.getD_cons_zero, word_gen] <;>
      ring
  · simp only [slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · show IsInK (σ (.n 14))
      rw [v]; exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _)
    · split <;> trivial

/-- Iteration `i`'s tree pops chunk `i`, then its tail's, every node exact. -/
theorem hs_post {f : Fn} (hfind : coreProgram.find? hsLoopName = some f) (hbody : f.body = hsLoopBody)
    (stream : E) (ws : List E) {n i : ℕ} (hi : i < n) (hn : n < 2 ^ 63) (rd : Reader)
    (hP : HsPre stream ws n rd) (ts : List Tree)
    (hv : Tree.KidsValid coreProgram rd (hsσ i n stream) (calls (hsLoopPre.flatMap (slEvs (hsσ i n stream)))) ts)
    (hq : KidsPost rd [HsPost ws (i + 1) n] (calls (hsLoopPre.flatMap (slEvs (hsσ i n stream)))) ts) :
    HsPost ws i n rd (.node hsLoopName (hsσ i n stream)
      (allocs (hsσ i n stream) (hsLoopPre.flatMap (slEvs (hsσ i n stream)))) ts) := by
  set σ := hsσ i n stream with hσ
  have v : ∀ j, σ (.n j) = (hsVals i n stream).getD j 0 := fun _ => rfl
  have hw : walk σ f.body = .ret (hsLoopPre.flatMap (slEvs σ)) [] := by
    rw [hbody, hsLoopBody]; exact walk_straight σ [] hsLoopPre hsLoopPre_straight
  have h14 : σ (.n 14) = 0 ↔ i + 1 = n := by
    rw [v]; exact gen_add_ne (by omega) (by omega)
  rw [hs_calls] at hv hq
  obtain ⟨t, rfl⟩ : ∃ t, ts = [t] := by
    rcases ts with _ | ⟨t, _ | ⟨t', ts⟩⟩
    · simp [Tree.KidsValid] at hv
    · exact ⟨t, rfl⟩
    · simp [Tree.KidsValid] at hv
  rw [Tree.KidsValid] at hv
  rw [kidsPost_cons] at hq
  have hk : t.pops coreProgram rd = (List.range (n - (i + 1))).map (fun j => ("stream", chunkOf ws (i + 1 + j))) ∧
      t.Every (ExactAt coreProgram rd) := by
    by_cases hl : i + 1 = n
    · have : decide (σ (.n 14) ≠ 0) = false := by simp [h14.mpr hl]
      have h1 := hv.2.1
      simp only [this, Bool.false_eq_true, ↓reduceIte] at h1
      obtain ⟨⟨g', σ', rfl⟩, -⟩ := h1
      refine ⟨by rw [Tree.pops, hl, Nat.sub_self]; rfl, Tree.every_phantom⟩
    · have : decide (σ (.n 14) ≠ 0) = true := by simp [h14, hl]
      exact hq.1 this
  have hch : Dest.words rd σ (.heap (.n 11) 0 256) = chunkOf ws i := by
    unfold Dest.words chunkOf
    refine List.map_congr_left fun k hk => ?_
    have hk' : k < 256 := List.mem_range.mp hk
    have hlt : 256 * i + k < ws.length := by rw [hP.2]; nlinarith
    have hl := hP.1 (256 * i + k) hlt
    rw [← loadHolds_mul_gen_pow] at hl
    rw [v, Nat.zero_add]
    simp only [hsVals, List.getD_cons_succ, List.getD_cons_zero]
    rw [hl.2, List.getD_eq_getElem _ _ hlt]
    rfl
  refine ⟨?_, ?_⟩
  · rw [Tree.pops_node hfind hw]
    simp only [Tree.popsKids]
    have hsp : ∀ (x : Ev), x = .skip hsLoopName [.n 16, .n 1, .n 2] ∨ x = .call hsLoopName [.n 16, .n 1, .n 2] [] →
        splice rd σ (hsLoopPre.flatMap (slEvs σ)) [t.pops coreProgram rd] =
          [("stream", Dest.words rd σ (.heap (.n 11) 0 256))] ++ t.pops coreProgram rd := by
      intro _ _
      simp only [hsLoopPre, hsLoopAtoms, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.flatMap_cons, List.flatMap_nil, slEvs, List.append_nil]
      split <;> simp [splice, Atom.pops, Hint.pops]
    rw [hsp _ (Or.inl rfl), hch, hk.1]
    rw [show n - i = n - (i + 1) + 1 by omega, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Nat.add_zero, List.singleton_append]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply]
    rw [show i + (j + 1) = i + 1 + j by omega]
  · rw [Tree.every_node]
    refine ⟨fun e he => ?_, by rw [Tree.EveryKids, Tree.EveryKids]; exact ⟨hk.2, trivial⟩⟩
    have hev' : Tree.events coreProgram (.node hsLoopName σ [] []) = hsLoopPre.flatMap (slEvs σ) := by
      simp only [Tree.events, Tree.name, Tree.val, hfind, hw]
    rw [hev'] at he
    cases e with
    | atom a =>
      have ha := hs_mem he
      simp only [hsLoopAtoms, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact trivial
    | _ => exact trivial

/-- The loop's heap hints: chunk `i`'s `256` cells. -/
theorem hs_hintAddrs (σ : Val) :
    heapHintAddrs σ (hsLoopPre.flatMap (slEvs σ)) =
      (List.range 256).map fun k => (σ (.n 11)).limb 0 * addressOfIndex (0 + k) := by
  simp only [heapHintAddrs, hsLoopPre, hsLoopAtoms, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.flatMap_cons, List.flatMap_nil, slEvs, List.append_nil]
  split <;> simp [Ev.hintAddrs, hintDest?, destHeap?]

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- **One iteration completes placed**, `m` iterations after it, the next one completing at the
next frame when `i + 1 < n`. -/
theorem hs_stepA {kd : ℕ} {f : Fn} (hfind : coreProgram.find? hsLoopName = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2]) (hbody : f.body = hsLoopBody)
    (hlp : coreProgram.loop hsLoopName = true) (s : ℕ) (ws : List E) {n : ℕ} (hn : n < 2 ^ 63)
    {R : ℕ → Prop} (hR : ∀ j < 256 * n, R (s + j)) (m i : ℕ) (hi : n = i + m + 1) (fp c : ℕ)
    (hfc : fp + (fs hsLoopName + hsB fs m) ≤ c)
    (hnext : i + 1 < n → CallAtA fs al cert kd hsLoopName [gen ^ (i + 1), gen ^ n, ptrAt s] [] R
      (fun _ => False) (fun _ => True) (HsPre (ptrAt s) ws n) (HsPost ws (i + 1) n) (hsB fs m)
      (fp + fs hsLoopName) c c) :
    CallAtA fs al cert kd hsLoopName [gen ^ i, gen ^ n, ptrAt s] [] R (fun _ => False) (fun _ => True)
      (HsPre (ptrAt s) ws n) (HsPost ws i n) (fs hsLoopName + hsB fs m) fp c c := by
  set σ := hsσ i n (ptrAt s) with hσ
  have v : ∀ j, σ (.n j) = (hsVals i n (ptrAt s)).getD j 0 := fun _ => rfl
  have hw : walk σ f.body = .ret (hsLoopPre.flatMap (slEvs σ)) [] := by
    rw [hbody, hsLoopBody]; exact walk_straight σ [] hsLoopPre hsLoopPre_straight
  have h14 : σ (.n 14) = 0 ↔ i + 1 = n := by
    rw [v]; exact gen_add_ne (by omega) (by omega)
  obtain ⟨hd, ha, hr, -⟩ := straight_parts σ hsLoopPre hsLoopPre_straight
  have hd' : allocDsts (hsLoopPre.flatMap (slEvs σ)) = [] := by rw [hd]; rfl
  have ha' : allocs σ (hsLoopPre.flatMap (slEvs σ)) = [] := by rw [ha]; rfl
  have hr' : addrs (hsLoopPre.flatMap (slEvs σ)) = [] := by rw [hr]; rfl
  have hlo : loadAddrs σ (hsLoopPre.flatMap (slEvs σ)) = [] := by
    rw [loadAddrs_straight σ hsLoopPre hsLoopPre_straight]; rfl
  have h11 : σ (.n 11) = ptrAt (s + 256 * i) := by
    rw [v]; simp only [hsVals, List.getD_cons_succ, List.getD_cons_zero]; rw [gen_pow_eq_ofK, ptrAt, ptrAt, ← ofK_mul, gpow_add']
  refine callAtA_nodeL (Bt := hsB fs m) hlp hfc ⟨σ, f, _, [], [], [HsPost ws (i + 1) n], fun _ => True,
    fun _ => False, hfind, by rw [hparams]; rfl, hw, rfl, ?_, ⟨by simp, List.Pairwise.nil⟩, ?_, ?_,
    fun _ h => h.elim, ?_, fun _ _ => trivial, fun rd _ _ _ => hs_events i n (ptrAt s) rd, ?_⟩
  · rw [ha']; exact ⟨by rw [hd']; rfl, by rw [hr']; simp⟩
  · intro A hA; rw [hlo] at hA; simp at hA
  · intro A hA
    rw [hs_hintAddrs, h11] at hA
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hA
    have hj' : j < 256 := List.mem_range.mp hj
    refine ⟨s + 256 * i + j, by rw [ptrAt, B1.Main.addr_ofK]; congr 1; omega, Or.inr (Or.inl ?_)⟩
    have := hR (256 * i + j) (by nlinarith)
    rwa [← Nat.add_assoc] at this
  · rw [ha', List.sum_nil, Nat.add_zero, hs_calls, KidsAtL]
    by_cases hl : i + 1 = n
    · have : decide (σ (.n 14) ≠ 0) = false := by simp [h14.mpr hl]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      obtain rfl : m = 0 := by omega
      exact ⟨⟨hsσ (i + 1) n (ptrAt s), f, hfind, by rw [hparams]; rfl⟩, rfl, rfl, fun _ _ => trivial,
        fun _ h => h.elim⟩
    · have : decide (σ (.n 14) ≠ 0) = true := by simp [h14, hl]
      simp only [this, ↓reduceIte, List.headD_cons]
      refine ⟨R, fun _ => False, fun _ => True, fun i h => Or.inl (Or.inl h), ?_, fun _ _ _ => trivial,
        fun _ h => h.elim⟩
      have e : [σ (.n 16), σ (.n 1), σ (.n 2)] = [gen ^ (i + 1), gen ^ n, ptrAt s] := rfl
      simp only [List.map_cons, List.map_nil, e]
      exact (hnext (by omega)).mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => h.1)
        (fun _ _ _ h => h)
  · intro rd ts _ hP _ hv hq
    exact hs_post hfind hbody (ptrAt s) ws (by omega) hn rd hP ts hv hq

/-- **The loop completes placed from iteration `i`**, `m` iterations after it. -/
theorem hs_loopA {kd : ℕ} {f : Fn} (hfind : coreProgram.find? hsLoopName = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2]) (hbody : f.body = hsLoopBody)
    (hlp : coreProgram.loop hsLoopName = true) (s : ℕ) (ws : List E) {n : ℕ} (hn : n < 2 ^ 63)
    {R : ℕ → Prop} (hR : ∀ j < 256 * n, R (s + j)) :
    ∀ m i, n = i + m + 1 → ∀ fp c, fp + (fs hsLoopName + hsB fs m) ≤ c →
      CallAtA fs al cert kd hsLoopName [gen ^ i, gen ^ n, ptrAt s] [] R (fun _ => False) (fun _ => True)
        (HsPre (ptrAt s) ws n) (HsPost ws i n) (fs hsLoopName + hsB fs m) fp c c := by
  intro m
  induction m with
  | zero =>
    intro i hi fp c hfc
    exact hs_stepA hfind hparams hbody hlp s ws hn hR 0 i hi fp c hfc fun h => absurd h (by omega)
  | succ m ih =>
    intro i hi fp c hfc
    exact hs_stepA hfind hparams hbody hlp s ws hn hR (m + 1) i hi fp c hfc fun _ =>
      ih (i + 1) (by omega) (fp + fs hsLoopName) c (by simp only [hsB] at hfc; omega)

/-- What `hint_stream`'s placed completeness gives. -/
def HintStreamCompleteA (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (kd : ℕ) : Prop :=
  ∀ (s : ℕ) (ws : List E) (n : ℕ) (R : ℕ → Prop), n < 2 ^ 63 → (∀ j < 256 * n, R (s + j)) →
    ∀ fp c, fp + fs "hint_stream" ≤ c →
      CallAtA fs al cert kd "hint_stream" [ptrAt s, gen ^ n] [] R (fun _ => False) (fun _ => True)
        (HsPre (ptrAt s) ws n)
        (fun rd t => t.pops coreProgram rd = (List.range n).map (fun j => ("stream", chunkOf ws j)) ∧
          t.Every (ExactAt coreProgram rd))
        (fs "hint_stream") fp c (allocBase (al hsLoopName) c + hsB fs n)

theorem hs_completeA {kd : ℕ} {f g : Fn} (hfind : coreProgram.find? hsLoopName = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2]) (hbody : f.body = hsLoopBody)
    (hlp : coreProgram.loop hsLoopName = true)
    (hfind' : coreProgram.find? "hint_stream" = some g) (hparams' : g.params = [.n 0, .n 1])
    (hbody' : g.body = hsBody) (hlp' : coreProgram.loop "hint_stream" = false) :
    HintStreamCompleteA fs al cert kd := by
  intro s ws n R hn hR fp c hfc
  let σ : Val := fun v => [ptrAt s, gen ^ n, 1, 1 + gen ^ n, 1].getD v.idx 0
  have hst : hsPre.all Stmt.straight = true := rfl
  have hw : walk σ g.body = .ret (hsPre.flatMap (slEvs σ)) [] := by
    rw [hbody', hsBody]; exact walk_straight σ [] hsPre hst
  have hcalls : calls (hsPre.flatMap (slEvs σ)) = [⟨hsLoopName, [.n 4, .n 1, .n 0], [], decide (σ (.n 3) ≠ 0)⟩] := by
    rw [(straight_parts σ hsPre hst).2.2.2]; rfl
  have h3 : σ (.n 3) = 0 ↔ n = 0 := by
    show (1 : E) + gen ^ n = 0 ↔ n = 0
    rw [← pow_zero gen, gen_add_ne (by omega) (by omega)]; omega
  obtain ⟨hd, ha, hr, -⟩ := straight_parts σ hsPre hst
  have hd' : allocDsts (hsPre.flatMap (slEvs σ)) = [] := by rw [hd]; rfl
  have ha' : allocs σ (hsPre.flatMap (slEvs σ)) = [] := by rw [ha]; rfl
  have hr' : addrs (hsPre.flatMap (slEvs σ)) = [] := by rw [hr]; rfl
  have hlo : loadAddrs σ (hsPre.flatMap (slEvs σ)) = [] := by rw [loadAddrs_straight σ hsPre hst]; rfl
  have hhi : heapHintAddrs σ (hsPre.flatMap (slEvs σ)) = [] := by
    simp only [heapHintAddrs, hsPre, List.flatMap_cons, List.flatMap_nil, slEvs, List.append_nil,
      List.cons_append, List.nil_append]
    split <;> simp [Ev.hintAddrs]
  refine callAtA_node hlp' hfc ⟨σ, g, _, [], [], [HsPost ws 0 n], fun _ => True, fun _ => False, hfind',
    by rw [hparams']; rfl, hw, rfl, ?_, ⟨by simp, List.Pairwise.nil⟩, ?_, ?_, fun _ h => h.elim, ?_,
    fun _ _ => trivial, ?_, ?_⟩
  · rw [ha']; exact ⟨by rw [hd']; rfl, by rw [hr']; simp⟩
  · intro A hA; rw [hlo] at hA; simp at hA
  · intro A hA; rw [hhi] at hA; simp at hA
  · rw [ha', List.sum_nil, Nat.add_zero, hcalls, KidsAtF]
    by_cases h0 : n = 0
    · have : decide (σ (.n 3) ≠ 0) = false := by simp [h3.mpr h0]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      refine ⟨⟨hsσ 0 n (ptrAt s), f, hfind, by rw [hparams]; simp [Tree.val, hsσ, hsVals]; exact ⟨rfl, rfl, rfl⟩⟩, ?_⟩
      rw [KidsAtF]
      exact ⟨by rw [h0]; rfl, fun _ _ => trivial, fun _ h => h.elim⟩
    · have : decide (σ (.n 3) ≠ 0) = true := by simp [h3, h0]
      simp only [this, ↓reduceIte, List.headD_cons]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      refine ⟨fs hsLoopName + hsB fs m, allocBase (al hsLoopName) c + (fs hsLoopName + hsB fs m), R,
        fun _ => False, fun _ => True, fun i h => Or.inl (Or.inl h), ?_, ?_⟩
      · have e : [σ (.n 4), σ (.n 1), σ (.n 0)] = [gen ^ 0, gen ^ (m + 1), ptrAt s] := by simp [σ]
        simp only [List.map_cons, List.map_nil, e]
        exact (hs_loopA hfind hparams hbody hlp s ws hn hR m 0 (by omega) _ _ le_rfl).mono
          (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => h.1) (fun _ _ _ h => h)
      · rw [KidsAtF]
        exact ⟨by simp only [hsB], fun _ _ => trivial, fun _ h => h.elim⟩
  · intro rd _ _ _ e he
    rw [List.mem_flatMap] at he
    obtain ⟨s', hs', he⟩ := he
    simp only [hsPre, List.mem_cons, List.not_mem_nil, or_false] at hs'
    rcases hs' with rfl | rfl | rfl | rfl
    · simp only [slEvs, List.mem_singleton] at he; subst he
      simp [Ev.Holds, Atom.Holds, σ, word_one]
    · simp only [slEvs, List.mem_singleton] at he; subst he
      simp [Ev.Holds, Atom.Holds, σ]
    · simp only [slEvs, List.mem_singleton] at he; subst he
      simp [Ev.Holds, Atom.Holds, σ, word_one]
    · simp only [slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · show IsInK (1 + gen ^ n)
        rw [← pow_zero gen]; exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _)
      · split <;> trivial
  · intro rd ts _ hP _ hv hq
    rw [hcalls] at hv hq
    rw [ha']
    obtain ⟨t, rfl⟩ : ∃ t, ts = [t] := by
      rcases ts with _ | ⟨t, _ | ⟨t', ts⟩⟩
      · simp [Tree.KidsValid] at hv
      · exact ⟨t, rfl⟩
      · simp [Tree.KidsValid] at hv
    rw [Tree.KidsValid] at hv
    rw [kidsPost_cons] at hq
    have hk : t.pops coreProgram rd = (List.range n).map (fun j => ("stream", chunkOf ws j)) ∧
        t.Every (ExactAt coreProgram rd) := by
      by_cases h0 : n = 0
      · have : decide (σ (.n 3) ≠ 0) = false := by simp [h3.mpr h0]
        have h1 := hv.2.1
        simp only [this, Bool.false_eq_true, ↓reduceIte] at h1
        obtain ⟨⟨g', σ', rfl⟩, -⟩ := h1
        exact ⟨by rw [Tree.pops, h0]; rfl, Tree.every_phantom⟩
      · have : decide (σ (.n 3) ≠ 0) = true := by simp [h3, h0]
        obtain ⟨h1, h2⟩ := hq.1 this
        refine ⟨by rw [h1, Nat.sub_zero]; simp, h2⟩
    refine ⟨?_, ?_⟩
    · rw [Tree.pops_node hfind' hw]
      simp only [Tree.popsKids, hsPre, List.flatMap_cons, List.flatMap_nil, slEvs, List.append_nil,
        List.cons_append, List.nil_append]
      rw [← hk.1]
      split <;> simp [splice, Atom.pops]
    · rw [Tree.every_node]
      refine ⟨fun e he => ?_, by rw [Tree.EveryKids, Tree.EveryKids]; exact ⟨hk.2, trivial⟩⟩
      have hev' : Tree.events coreProgram (.node "hint_stream" σ [] []) = hsPre.flatMap (slEvs σ) := by
        simp only [Tree.events, Tree.name, Tree.val, hfind', hw]
      rw [hev'] at he
      simp only [hsPre, List.flatMap_cons, List.flatMap_nil, slEvs, List.append_nil, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | he
      · exact trivial
      · exact trivial
      · exact trivial
      · exact trivial
      · split at he <;> (subst he; exact trivial)

set_option maxRecDepth 100000 in
/-- **`hint_stream` completes placed**, popping the stream's chunks in order. -/
theorem hint_stream_completeA (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (kd : ℕ) :
    HintStreamCompleteA fs al cert kd :=
  hs_completeA (f := fn% «hint_stream_loop0») (g := fn% «hint_stream»)
    (coreProgram_find?_at (j := idx% «hint_stream_loop0») rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (by rw [Program.loop_of_find? (coreProgram_find?_at (j := idx% «hint_stream_loop0») rfl)]; decide +kernel)
    (coreProgram_find?_at (j := idx% «hint_stream») rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (by rw [Program.loop_of_find? (coreProgram_find?_at (j := idx% «hint_stream») rfl)]; decide +kernel)

end
end LeanVM.Guest.B1.VsC
