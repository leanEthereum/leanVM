/-
  LeanVM.Guest.B1.VsC.HintStreamC

  `hint_stream` completes, layout-free, popping the stream's chunks.
-/

module

public import LeanVM.Guest.B1.VsC.Fwd
public import LeanVM.Guest.Complete.Compose
public import LeanVM.Guest.Memory.Straight
public import LeanVM.Guest.B1.VsC.Mono
import LeanVM.Guest.CoreRef

/-!
# `hint_stream`, complete

`hint_stream(stream, n_g)` runs its loop `__loop0_hint_stream(xc, n_g, stream)` from `xc = g^0`
while `xc ≠ n_g`: iteration `i` pops the `stream` witness's chunk into the `256` words at
`stream·g^(256 i)`, then steps `xc` by `g`. A witness hint into the heap constrains nothing; it pops
the words the memory holds there. So on every memory holding the `256 n` words `ws` at `stream`,
`n < 2^63`, the call returns, its tree popping `("stream", chunk i)` for `i < n` in order, every node
exact (`hint_stream_complete`). The loop's iterations are `hs_loop`, from the last down.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Protocol.Verifier LeanVM.Guest.Value

@[expose] public section

/-- The loop's name. -/
abbrev hsLoopName : String := "__loop0_hint_stream"

/-- The loop's atoms. -/
def hsLoopAtoms : List Atom :=
  [.mul (.n 3) (.n 0) (.n 0), .mul (.n 4) (.n 3) (.n 3), .mul (.n 5) (.n 4) (.n 4),
    .mul (.n 6) (.n 5) (.n 5), .mul (.n 7) (.n 6) (.n 6), .mul (.n 8) (.n 7) (.n 7),
    .mul (.n 9) (.n 8) (.n 8), .mul (.n 10) (.n 9) (.n 9), .mul (.n 11) (.n 2) (.n 10),
    .hint (.witness "stream" (.heap (.n 11) 0 256)),
    .const (.n 12) (word 2 0), .mul (.n 13) (.n 0) (.n 12), .add (.n 14) (.n 13) (.n 1),
    .const (.n 15) (word 2 0), .mul (.n 16) (.n 0) (.n 15)]

/-- The loop's straight part. -/
def hsLoopPre : List Stmt := hsLoopAtoms.map Stmt.atom ++ [.callIf (.n 14) hsLoopName [.n 16, .n 1, .n 2]]

/-- The loop's body. -/
def hsLoopBody : List Stmt := hsLoopPre ++ [.ret []]

/-- `hint_stream`'s straight part. -/
def hsPre : List Stmt :=
  [.atom (.const (.n 2) (word 1 0)), .atom (.add (.n 3) (.n 2) (.n 1)), .atom (.const (.n 4) (word 1 0)),
    .callIf (.n 3) hsLoopName [.n 4, .n 1, .n 0]]

/-- `hint_stream`'s body. -/
def hsBody : List Stmt := hsPre ++ [.ret []]

/-- Chunk `i` of the stream: its `256` words from `256 i`. -/
def chunkOf (ws : List E) (i : ℕ) : List E := (List.range 256).map fun k => ws.getD (256 * i + k) 0

/-- The memory holds the stream's `256 n` words at `stream`. -/
def HsPre (stream : E) (ws : List E) (n : ℕ) (rd : Reader) : Prop := ReadsAt rd stream ws ∧ ws.length = 256 * n

/-- The chunks from `i` on, popped in order, every node exact. -/
def HsPost (ws : List E) (i n : ℕ) (rd : Reader) (t : Tree) : Prop :=
  t.pops coreProgram rd = (List.range (n - i)).map (fun j => ("stream", chunkOf ws (i + j))) ∧
    t.Every (ExactAt coreProgram rd)

/-- Iteration `i`'s words. -/
def hsVals (i n : ℕ) (stream : E) : List E :=
  [gen ^ i, gen ^ n, stream, gen ^ (2 * i), gen ^ (4 * i), gen ^ (8 * i), gen ^ (16 * i), gen ^ (32 * i),
    gen ^ (64 * i), gen ^ (128 * i), gen ^ (256 * i), stream * gen ^ (256 * i), gen, gen ^ (i + 1),
    gen ^ (i + 1) + gen ^ n, gen, gen ^ (i + 1)]

/-- Iteration `i`'s valuation. -/
def hsσ (i n : ℕ) (stream : E) : Val := fun v => (hsVals i n stream).getD v.idx 0

theorem hsLoopPre_straight : hsLoopPre.all Stmt.straight = true := rfl

theorem hs_calls (σ : Val) :
    calls (hsLoopPre.flatMap (slEvs σ)) = [⟨hsLoopName, [.n 16, .n 1, .n 2], [], decide (σ (.n 14) ≠ 0)⟩] := by
  rw [(straight_parts σ hsLoopPre hsLoopPre_straight).2.2.2]
  rfl

theorem hs_mem {a : Atom} {σ : Val} (h : Ev.atom a ∈ hsLoopPre.flatMap (slEvs σ)) : a ∈ hsLoopAtoms := by
  simp only [hsLoopPre, List.flatMap_append, List.mem_append, List.flatMap_map] at h
  rcases h with h | h
  · simpa [slEvs] using h
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, slEvs, List.mem_cons,
      List.not_mem_nil, or_false] at h
    rcases h with h | h
    · cases h
    · split at h <;> cases h

theorem gen_add_ne {a b : ℕ} (ha : a < 2 ^ 64 - 1) (hb : b < 2 ^ 64 - 1) :
    gen ^ a + gen ^ b = 0 ↔ a = b := by
  refine ⟨fun h => gen_pow_inj ha hb (CharTwo.add_eq_zero.mp h), fun h => ?_⟩
  rw [h]; exact CharTwo.add_self_eq_zero _

/-- **One iteration completes**, the next one completing when `i + 1 < n`. -/
theorem hs_step {kd : ℕ} {f : Fn} (hfind : coreProgram.find? hsLoopName = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2]) (hbody : f.body = hsLoopBody)
    (stream : E) (ws : List E) {n i : ℕ} (hi : i < n) (hn : n < 2 ^ 63)
    (hnext : i + 1 < n → CallCompletes kd hsLoopName [gen ^ (i + 1), gen ^ n, stream] []
      (HsPre stream ws n) (HsPost ws (i + 1) n)) :
    CallCompletes kd hsLoopName [gen ^ i, gen ^ n, stream] [] (HsPre stream ws n) (HsPost ws i n) := by
  set σ := hsσ i n stream with hσ
  have v : ∀ j, σ (.n j) = (hsVals i n stream).getD j 0 := fun _ => rfl
  have hw : walk σ f.body = .ret (hsLoopPre.flatMap (slEvs σ)) [] := by
    rw [hbody, hsLoopBody]; exact walk_straight σ [] hsLoopPre hsLoopPre_straight
  have h14 : σ (.n 14) = 0 ↔ i + 1 = n := by
    rw [v]; exact gen_add_ne (by omega) (by omega)
  refine callCompletes_node fun b => ⟨0, [], σ, f, hsLoopPre.flatMap (slEvs σ), [], [HsPost ws (i + 1) n],
    wordsIn_nil b, hfind, by rw [hparams]; rfl, hw, rfl, fun rd _ _ hP e he => ?_, ?_, ?_⟩
  · -- the events hold
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
  · -- the callee
    rw [hs_calls]
    refine ⟨?_, trivial⟩
    by_cases hl : i + 1 = n
    · have : decide (σ (.n 14) ≠ 0) = false := by simp [h14.mpr hl]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hsσ (i + 1) n stream, f, hfind, by rw [hparams]; rfl⟩
    · have : decide (σ (.n 14) ≠ 0) = true := by simp [h14, hl]
      simp only [this, ↓reduceIte, List.headD_cons]
      exact (hnext (by omega)).mono' fun rd h => h.2
  · -- the pops and exactness
    intro rd ts _ _ hP hv hq
    rw [hs_calls] at hv hq
    obtain ⟨t, rfl⟩ : ∃ t, ts = [t] := by
      rcases ts with _ | ⟨t, _ | ⟨t', ts⟩⟩
      · simp [Tree.KidsValid] at hv
      · exact ⟨t, rfl⟩
      · simp [Tree.KidsValid] at hv
    rw [Tree.KidsValid] at hv
    rw [kidsPost_cons] at hq
    -- the callee's pops and exactness
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
    -- the witness's words are chunk `i`
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
    have hev : Tree.events coreProgram (.node hsLoopName σ (allocs σ (hsLoopPre.flatMap (slEvs σ))) [t]) =
        hsLoopPre.flatMap (slEvs σ) := by
      simp only [Tree.events, Tree.name, Tree.val, hfind, hw]
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

/-- **The loop completes from iteration `i`**, every `i < n`. -/
theorem hs_loop {kd : ℕ} {f : Fn} (hfind : coreProgram.find? hsLoopName = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2]) (hbody : f.body = hsLoopBody)
    (stream : E) (ws : List E) {n : ℕ} (hn : n < 2 ^ 63) :
    ∀ m i, n = i + m + 1 → CallCompletes kd hsLoopName [gen ^ i, gen ^ n, stream] []
      (HsPre stream ws n) (HsPost ws i n) := by
  intro m
  induction m with
  | zero => intro i hi; exact hs_step hfind hparams hbody stream ws (by omega) hn fun h => absurd h (by omega)
  | succ m ih =>
    intro i hi
    exact hs_step hfind hparams hbody stream ws (by omega) hn fun _ => ih (i + 1) (by omega)

/-- What `hint_stream`'s completeness gives. -/
def HintStreamComplete (kd : ℕ) : Prop :=
  ∀ (stream : E) (ws : List E) (n : ℕ), n < 2 ^ 63 →
    CallCompletes kd "hint_stream" [stream, gen ^ n] [] (HsPre stream ws n)
      (fun rd t => t.pops coreProgram rd = (List.range n).map (fun j => ("stream", chunkOf ws j)) ∧
        t.Every (ExactAt coreProgram rd))

theorem hs_complete {kd : ℕ} {f g : Fn} (hfind : coreProgram.find? hsLoopName = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2]) (hbody : f.body = hsLoopBody)
    (hfind' : coreProgram.find? "hint_stream" = some g) (hparams' : g.params = [.n 0, .n 1])
    (hbody' : g.body = hsBody) : HintStreamComplete kd := by
  intro stream ws n hn
  let σ : Val := fun v => [stream, gen ^ n, 1, 1 + gen ^ n, 1].getD v.idx 0
  have hst : hsPre.all Stmt.straight = true := rfl
  have hw : walk σ g.body = .ret (hsPre.flatMap (slEvs σ)) [] := by
    rw [hbody', hsBody]; exact walk_straight σ [] hsPre hst
  have hcalls : calls (hsPre.flatMap (slEvs σ)) = [⟨hsLoopName, [.n 4, .n 1, .n 0], [], decide (σ (.n 3) ≠ 0)⟩] := by
    rw [(straight_parts σ hsPre hst).2.2.2]; rfl
  have h3 : σ (.n 3) = 0 ↔ n = 0 := by
    show (1 : E) + gen ^ n = 0 ↔ n = 0
    rw [← pow_zero gen, gen_add_ne (by omega) (by omega)]; omega
  refine callCompletes_node fun b => ⟨0, [], σ, g, hsPre.flatMap (slEvs σ), [], [HsPost ws 0 n],
    wordsIn_nil b, hfind', by rw [hparams']; rfl, hw, rfl, fun rd _ _ hP e he => ?_, ?_, ?_⟩
  · rw [List.mem_flatMap] at he
    obtain ⟨s, hs, he⟩ := he
    simp only [hsPre, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
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
  · rw [hcalls]
    refine ⟨?_, trivial⟩
    by_cases h0 : n = 0
    · have : decide (σ (.n 3) ≠ 0) = false := by simp [h3.mpr h0]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hsσ 0 n stream, f, hfind, by rw [hparams]; simp [Tree.val, hsσ, hsVals]; exact ⟨rfl, rfl, rfl⟩⟩
    · have : decide (σ (.n 3) ≠ 0) = true := by simp [h3, h0]
      simp only [this, ↓reduceIte, List.headD_cons]
      have e : [σ (.n 4), σ (.n 1), σ (.n 0)] = [gen ^ 0, gen ^ n, stream] := by simp [σ]
      simp only [List.map_cons, List.map_nil, e]
      exact (hs_loop hfind hparams hbody stream ws hn (n - 1) 0 (by omega)).mono' fun rd h => h.2
  · intro rd ts _ _ hP hv hq
    rw [hcalls] at hv hq
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
/-- **`hint_stream` completes**, popping the stream's chunks in order. -/
theorem hint_stream_complete (kd : ℕ) : HintStreamComplete kd :=
  hs_complete (f := fn% «hint_stream_loop0») (g := fn% «hint_stream»)
    (coreProgram_find?_at (j := idx% «hint_stream_loop0») rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (coreProgram_find?_at (j := idx% «hint_stream») rfl) rfl (stmtsEqb_sound (by decide +kernel))

end
end LeanVM.Guest.B1.VsC
