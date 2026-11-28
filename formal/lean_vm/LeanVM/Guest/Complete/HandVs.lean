/-
  LeanVM.Guest.Complete.HandVs

  What `verify_sub` certifies of a child's shape, at every node of `main`'s honest tree (`vsVals`):
  its hinted shape values are an accepted child's, and it passes the Keccak table's log and the
  stack's kappas down to `verify_keccak` and `check_stack_terminal`.
-/

module

public import LeanVM.Guest.Complete.HandLoopMeta
public import LeanVM.Guest.Complete.CycThen
public import LeanVM.Guest.Budget.HandPre
public import LeanVM.Guest.B1.VsC.VsOrcFront
public import LeanVM.Guest.B1.VerifySub.Flat

/-!
# `verify_sub`'s values

* The honest side: a `stream_chunks`, `table_logs` or `link_shape` entry of `honestPushes` is an
  accepted child's (`honest_proofEntry`), so by `frontNum_of_child` its chunk count is at most `32`, its
  heights at most `24` (the Keccak table's at least `9`), its tallest height at most `24` and its pointer
  width within `19 ..= 24`, and the packed challenges' permutations at most `19` (`packed_le`).
* `verify_sub`'s path: its hints are among its path's entries and its loads read their words
  (`vs_atom`, `heap_words_getD`), so its values are those (`vs_node`).
* Down the tree (`vsPreIn`): `verify_sub` is the only caller of `verify_keccak` and `check_stack_terminal`
  (`calleesVs_of_find`, `loop_callees`), and calls them at its `v120 = g^τ` and its `kappa_base`
  buffer, whose word `7` is `v120` (`vs_sites`, by the kernel over its call sites).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Guest.Budget LeanVM.Guest.Value

@[expose] public section

/-! ## The honest entries of a child's proof -/

/-- The streams only a child's proof's hints push and `verify_sub` reads. -/
def proofNames : List String := ["stream_chunks", "table_logs", "link_shape"]

/-- The streams of a Merkle phase's hints. -/
def mkNames : List String := ["merkle_leaf_rows", "merkle_children", "merkle_caps", "merkle_cap_active"]

theorem levelHints_mk (first : Bool) (depth count : ℕ) (phase : List LeanVM.Protocol.Compile.Opening) :
    ∀ p ∈ Prover.levelHints first depth count phase, p.1 ∈ mkNames := by
  intro p hp
  simp only [Prover.levelHints, List.mem_append, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with ⟨x, -, hx⟩ | rfl | rfl
  · obtain ⟨o, steps, r⟩ := x
    rcases hx with rfl | rfl <;> simp [mkNames]
  · simp [mkNames]
  · simp [mkNames]

theorem merkleHints_mk : ∀ (first : Bool) (qs : List (ℕ × List ℕ))
    (ps : List (List LeanVM.Protocol.Compile.Opening)), ∀ p ∈ Prover.merkleHints first qs ps, p.1 ∈ mkNames
  | first, (d, pos) :: rest, ph :: phs => by
      intro p hp
      rw [Prover.merkleHints, List.mem_append] at hp
      rcases hp with hp | hp
      · exact levelHints_mk first d pos.length ph p hp
      · exact merkleHints_mk false rest phs p hp
  | _, [], _ => by intro p hp; simp [Prover.merkleHints] at hp
  | _, _ :: _, [] => by intro p hp; simp [Prover.merkleHints] at hp

theorem childSlotPushes_notProof (os : List ℕ) : ∀ p ∈ Prover.childSlotPushes os, p.1 ∉ proofNames := by
  intro p hp
  unfold Prover.childSlotPushes at hp
  split_ifs at hp
  · simp at hp
  · simp only [List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | rfl | ⟨_, -, rfl⟩ <;> simp [proofNames]
  · simp only [List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | rfl | ⟨_, -, rfl⟩ <;> simp [proofNames]

theorem pre_notProof : ∀ a ∈ preNames, a ∉ proofNames := by decide
theorem da_notProof : ∀ a ∈ daNames, a ∉ proofNames := by decide

/-- **An entry of a child's proof's streams is a child's hint.** -/
theorem honest_proofEntry (s : NodeStatement) (w : NodeWitness) {p : Pop}
    (hp : p ∈ Prover.honestPushes guestBytecode guestSeed s w) (hn : p.1 ∈ proofNames) :
    ∃ c ∈ w.children, p ∈ Prover.childHints guestBytecode guestSeed c := by
  rw [honest_eq] at hp
  simp only [List.mem_append] at hp
  rcases hp with (((hp | hp) | hp) | hp) | hp
  · exact absurd hn (pre_notProof _ (preX_names s w p hp))
  · obtain ⟨⟨⟨c, xs⟩, ss⟩, hm, hp⟩ := List.mem_flatMap.mp hp
    dsimp only at hp
    have hc := (List.of_mem_zip (List.of_mem_zip hm).1).1
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · rcases List.mem_append.mp hp with hp | hp
        · rcases List.mem_cons.mp hp with rfl | hp
          · simp [proofNames] at hn
          · exact absurd hn (childSlotPushes_notProof xs p hp)
        · exact absurd hn (childSlotPushes_notProof ss p hp)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> simp [proofNames] at hn
    · exact ⟨c, hc, hp⟩
  · unfold mLA at hp
    split_ifs at hp
    · rw [List.mem_singleton] at hp; subst hp; simp [proofNames] at hn
    · simp only [Prover.batchPushes, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl <;> simp [proofNames] at hn
  · unfold mDA at hp
    cases hm : w.daMatrix with
    | none => simp [hm] at hp
    | some cm =>
      rw [hm] at hp
      exact absurd hn (da_notProof _ (daHints_names cm.1 cm.2 p hp))
  · rw [List.mem_singleton] at hp; subst hp; simp [proofNames] at hn

theorem foldl_add_eq_sum : ∀ (l : List ℕ) (a : ℕ), l.foldl (· + ·) a = a + l.sum
  | [], a => by simp
  | x :: l, a => by rw [List.foldl_cons, foldl_add_eq_sum l, List.sum_cons]; omega

/-- **A child's hints of the three streams**, at its announced layout. -/
theorem childHints_proof {c : Child} {layout : Layout} {r : ℕ}
    (hann : announcedLayoutAndRate guestBytecode c.proof.stream = some (layout, r)) {p : Pop}
    (hp : p ∈ Prover.childHints guestBytecode guestSeed c) :
    (p.1 = "stream_chunks" → p.2 = [Prover.count (VsC.chunksOf c.proof.stream.length)]) ∧
    (p.1 = "table_logs" → p.2 = layout.tableLogHeights.map Prover.count) ∧
    (p.1 = "link_shape" → ∃ b, p.2 = [Prover.count (VsC.hMax layout), Prover.count (VsC.widthOf layout), b,
      Prover.count ((packedChallenges tables (VsC.hMax layout) (VsC.widthOf layout) + 7) / 8)]) := by
  have hw : pointerWidth layout.logMemory layout.logBytecode layout.tableRows.sum = VsC.widthOf layout := by
    rw [VsC.widthOf, VsC.cyclesOf, foldl_add_eq_sum, Nat.zero_add]
  unfold Prover.childHints at hp
  rw [hann] at hp
  dsimp only at hp
  rw [hw] at hp
  simp only [List.mem_append] at hp
  rcases hp with ((((hp | hp) | hp) | hp) | hp) | hp
  · rw [List.mem_singleton] at hp; subst hp
    refine ⟨fun _ => rfl, fun h => by simp at h, fun h => by simp at h⟩
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
    refine ⟨fun h => by simp at h, fun h => by simp at h, fun h => by simp at h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨fun h => by simp at h, fun _ => rfl, fun h => by simp at h⟩
    · exact ⟨fun h => by simp at h, fun h => by simp at h, fun _ => ⟨_, rfl⟩⟩
  · simp only [Prover.stackHints, List.mem_singleton] at hp; subst hp
    exact ⟨fun h => by simp at h, fun h => by simp at h, fun h => by simp at h⟩
  · rw [List.mem_singleton] at hp; subst hp
    exact ⟨fun h => by simp at h, fun h => by simp at h, fun h => by simp at h⟩
  · have := merkleHints_mk _ _ _ p hp
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [h] at this <;> exact absurd this (by decide)

/-- **The shape values `verify_sub` reads, from the honest pushes.** -/
structure ProofVals (p : Pop) : Prop where
  chunks : p.1 = "stream_chunks" → ∃ n ≤ 32, p.2 = [Prover.count n]
  logs : p.1 = "table_logs" → ∃ hs : List ℕ, p.2 = hs.map Prover.count ∧ (∀ t < 6, hs.getD t 0 ≤ 24) ∧
    9 ≤ hs.getD 5 0
  shape : p.1 = "link_shape" → ∃ n wd b, n ≤ 24 ∧ 19 ≤ wd ∧ wd ≤ 24 ∧
    p.2 = [Prover.count n, Prover.count wd, b, Prover.count ((packedChallenges tables n wd + 7) / 8)]

theorem proofVals_of {w : NodeWitness} (hch : ChildrenOk guestBytecode guestSeed w) {s : NodeStatement} {p : Pop}
    (hp : p ∈ Prover.honestPushes guestBytecode guestSeed s w) : ProofVals p := by
  by_cases hn : p.1 ∈ proofNames
  swap
  · exact ⟨fun h => (hn (by simp [h, proofNames])).elim, fun h => (hn (by simp [h, proofNames])).elim,
      fun h => (hn (by simp [h, proofNames])).elim⟩
  obtain ⟨c, hc, hpc⟩ := honest_proofEntry s w hp hn
  obtain ⟨layout, r, hann, -, F⟩ := VsC.frontNum_of_child (vsChildOk_of_acceptable (hch c hc))
  obtain ⟨h1, h2, h3⟩ := childHints_proof hann hpc
  have hmax : VsC.hMax layout ≤ 24 := by
    obtain ⟨t, ht, he⟩ := F.hn
    rw [← he]; exact F.h24 t ht
  refine ⟨fun h => ⟨_, F.hp, h1 h⟩, fun h => ⟨_, h2 h, F.h24, F.h9⟩, fun h => ?_⟩
  obtain ⟨b, hb⟩ := h3 h
  exact ⟨_, _, b, hmax, F.hw19, F.hw24, hb⟩

theorem packed_n (n wd : ℕ) : packedChallenges tables n wd = packedChallenges tables 0 wd + n := by
  simp only [packedChallenges]; omega

set_option maxRecDepth 100000 in
theorem packed_w : ∀ wd < 25, 19 ≤ wd → packedChallenges tables 0 wd + 24 ≤ 152 := by
  decide +kernel

theorem packed_le {n wd : ℕ} (hn : n ≤ 24) (h19 : 19 ≤ wd) (h24 : wd ≤ 24) :
    (packedChallenges tables n wd + 7) / 8 ≤ 19 := by
  have := packed_w wd (by omega) h19
  rw [packed_n]
  omega

/-! ## Call sites -/

mutual
/-- The calls a statement can make, with their arguments. -/
def Stmt.sitesH : Stmt → List (String × List V)
  | .ite _ z n => Stmt.blockSitesH z ++ Stmt.blockSitesH n
  | .match_ _ arms => Stmt.armsSitesH arms
  | .call f args _ => [(f, args)]
  | .callIf _ f args => [(f, args)]
  | .dispatch _ fs args _ => fs.map fun f => (f, args)
  | _ => []

/-- The calls a block can make, with their arguments. -/
def Stmt.blockSitesH : List Stmt → List (String × List V)
  | [] => []
  | s :: ss => Stmt.sitesH s ++ Stmt.blockSitesH ss

/-- The calls any arm can make, with their arguments. -/
def Stmt.armsSitesH : List (List Stmt) → List (String × List V)
  | [] => []
  | a :: as => Stmt.blockSitesH a ++ Stmt.armsSitesH as
end

section Sites

variable {σ : Val}

theorem pick_sites {x : V} {args rets : List V} : ∀ (gs : List String) (j : ℕ),
    ∀ c ∈ calls (pick σ x args rets j gs).evs, (c.f, c.args) ∈ gs.map fun f => (f, args)
  | [], _ => by simp [pick, Out.evs, calls]
  | g :: gs, j => by
      unfold pick
      split_ifs
      · simp [Out.evs, calls, Ev.call?]
      · exact fun c hc => List.mem_cons_of_mem _ (pick_sites gs (j + 1) c hc)

mutual
theorem walk1_sites : ∀ (s : Stmt) {c : Call}, c ∈ calls (walk1 σ s).evs → (c.f, c.args) ∈ Stmt.sitesH s
  | .atom a, c, h => by simp [walk1, Out.evs, calls, Ev.call?] at h
  | .ite b z m, c, h => by
      rw [walk1, Out.calls_pre_inK] at h
      simp only [Stmt.sitesH, List.mem_append]
      split_ifs at h
      · exact Or.inl (walk_sites z h)
      · exact Or.inr (walk_sites m h)
  | .match_ x arms, c, h => by
      rw [walk1] at h
      exact walkArms_sites x arms 0 h
  | .call f args rets, c, h => by
      simp only [walk1, Out.evs, calls, List.filterMap_cons, Ev.call?, List.filterMap_nil,
        List.mem_cons, List.not_mem_nil, or_false] at h
      subst h; simp [Stmt.sitesH]
  | .callIf b f args, c, h => by
      rw [walk1] at h
      split_ifs at h <;>
        simp only [Out.evs, calls, List.filterMap_cons, Ev.call?, List.filterMap_nil,
          List.mem_cons, List.not_mem_nil, or_false] at h <;> subst h <;> simp [Stmt.sitesH]
  | .dispatch x gs args rets, c, h => by
      rw [walk1] at h
      exact pick_sites gs 0 c h
  | .ret _, c, h => by simp [walk1, Out.evs, calls] at h

/-- **A block's path calls its call sites.** -/
theorem walk_sites : ∀ (ss : List Stmt) {c : Call}, c ∈ calls (walk σ ss).evs → (c.f, c.args) ∈ Stmt.blockSitesH ss
  | [], c, h => by simp [walk, Out.evs, calls] at h
  | s :: ss, c, h => by
      rw [walk] at h
      simp only [Stmt.blockSitesH, List.mem_append]
      rcases Out.calls_seq h with h | h
      · exact Or.inl (walk1_sites s h)
      · exact Or.inr (walk_sites ss h)

theorem walkArms_sites (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ) {c : Call},
    c ∈ calls (walkArms σ x j arms).evs → (c.f, c.args) ∈ Stmt.armsSitesH arms
  | [], _, c, h => by simp [walkArms, Out.evs, calls] at h
  | a :: as, j, c, h => by
      unfold walkArms at h
      simp only [Stmt.armsSitesH, List.mem_append]
      split_ifs at h
      · exact Or.inl (walk_sites a h)
      · exact Or.inr (walkArms_sites x as (j + 1) h)
end

end Sites

/-- `verify_keccak`'s arguments at `verify_sub`'s call. -/
def vkArgs : List V :=
  [.n 1288, .n 1289, .n 1290, .n 1291, .n 1292, .n 2910, .n 120, .n 15, .n 2912, .n 20, .n 21, .n 2914]

/-- `verify_sub`'s calls of `verify_keccak` and `check_stack_terminal`: `v120` sixth, `v112` second, `v408`
sixth. -/
def vsSiteOk (x : String × List V) : Bool :=
  (x.1 != "verify_keccak" || x.2 == vkArgs) && (x.1 != "check_stack_terminal" || x.2.take 7 == [.n 4, .n 112, .n 486, .n 487, .n 485, .n 15, .n 408])

set_option maxRecDepth 200000 in
theorem vs_sites : (Stmt.blockSitesH (fn% «verify_sub»).body).all vsSiteOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem loop_callees : (Stmt.blockCallees (coreProgram[Data.chidxLoop]'ch_nodeIdx.hl).body).all
    (fun g => g != "verify_keccak" && g != "check_stack_terminal") = true := by decide +kernel

/-! ## Paths -/

section Paths

variable {σ : Val}

/-- An atom of a block that falls through is on its path. -/
theorem atom_mem_of_fall {a : Atom} : ∀ {ss : List Stmt} {es : List Ev}, walk σ ss = .fall es →
    Stmt.atom a ∈ ss → Ev.atom a ∈ es
  | [], _, _, hm => absurd hm List.not_mem_nil
  | s :: ss, es, hw, hm => by
      rw [walk] at hw
      cases h1 : walk1 σ s with
      | fall es1 =>
        rw [h1] at hw
        cases h2 : walk σ ss with
        | fall es2 =>
          rw [h2] at hw
          simp only [Out.seq, Out.pre, Out.fall.injEq] at hw
          subst hw
          rcases List.mem_cons.mp hm with rfl | hm
          · simp only [walk1, Out.fall.injEq] at h1
            subst h1
            exact List.mem_append_left _ List.mem_cons_self
          · exact List.mem_append_right _ (atom_mem_of_fall h2 hm)
        | ret _ _ => rw [h2] at hw; simp [Out.seq, Out.pre] at hw
        | stuck => rw [h2] at hw; simp [Out.seq, Out.pre] at hw
      | ret _ _ => rw [h1] at hw; simp [Out.seq] at hw
      | stuck => rw [h1] at hw; simp [Out.seq] at hw

/-- **An atom of a return-free prefix is on a returning path.** -/
theorem atom_mem_walk {a : Atom} {pre rest : List Stmt} {es : List Ev} {vs : List V}
    (hn : Stmt.noRetListS pre = true) (hw : walk σ (pre ++ rest) = .ret es vs) (ha : Stmt.atom a ∈ pre) :
    Ev.atom a ∈ es := by
  rw [walk_append] at hw
  rcases walk_noRet pre hn with ⟨es0, h0⟩ | h0
  · rw [h0] at hw
    cases hr : walk σ rest with
    | ret es' vs' =>
      rw [hr] at hw
      simp only [Out.seq, Out.pre, Out.ret.injEq] at hw
      rw [← hw.1]
      exact List.mem_append_left _ (atom_mem_of_fall h0 ha)
    | fall _ => rw [hr] at hw; simp [Out.seq, Out.pre] at hw
    | stuck => rw [hr] at hw; simp [Out.seq, Out.pre] at hw
  · rw [h0] at hw; simp [Out.seq] at hw

theorem mem_of_drop_take {L : List Stmt} {i : ℕ} {s : Stmt} (h : (L.drop i).take 1 = [s]) : s ∈ L :=
  List.mem_of_mem_drop (List.mem_of_mem_take (by rw [h]; exact List.mem_singleton_self _))

theorem mem_of_drop_eq {L M : List Stmt} {i : ℕ} (h : L.drop i = M) {s : Stmt} (hs : s ∈ M) : s ∈ L :=
  List.mem_of_mem_drop (by rw [h]; exact hs)

end Paths

theorem vsPre_noRetS : Stmt.noRetListS VerifySub.vsPre = true := by decide +kernel

theorem vsS24 : (VerifySub.vsPre.drop 24).take 1 = [.atom (.hint (.witness "stream_chunks" (.stack [.n 42])))] :=
  stmtsEqb_sound (by decide +kernel)
theorem vsS81 : (VerifySub.vsPre.drop 81).take 1 = [.atom (.hint (.witness "table_logs" (.heap (.n 6) 0 6)))] :=
  stmtsEqb_sound (by decide +kernel)
theorem vsS90 : (VerifySub.vsPre.drop 90).take 1 = [.atom (.load (.n 120) (.n 6) 5)] :=
  stmtsEqb_sound (by decide +kernel)
theorem vsS98 : (VerifySub.vsPre.drop 98).take 1 = [.atom (.load (.n 120) (.n 112) 7)] :=
  stmtsEqb_sound (by decide +kernel)
theorem vsS375 : (VerifySub.vsPre.drop 375).take 1 = [.atom (.hint (.witness "link_shape" (.heap (.n 9) 0 4)))] :=
  stmtsEqb_sound (by decide +kernel)
theorem vsS376 : (VerifySub.vsPre.drop 376).take 1 = [.atom (.load (.n 408) (.n 9) 0)] :=
  stmtsEqb_sound (by decide +kernel)
theorem vsS377 : (VerifySub.vsPre.drop 377).take 1 = [.atom (.load (.n 409) (.n 9) 1)] :=
  stmtsEqb_sound (by decide +kernel)
theorem vsS537 : (VerifySub.vsPre.drop 537).take 1 = [.atom (.load (.n 645) (.n 9) 3)] :=
  stmtsEqb_sound (by decide +kernel)

variable {rd : Reader} {H : List Pop}

/-- An atom of `verify_sub`'s return-free part is on its path. -/
theorem vs_atom {σ : Val} {es : List Ev} {vs : List V} (hw : walk σ (fn% «verify_sub»).body = .ret es vs)
    {i : ℕ} {a : Atom} (h : (VerifySub.vsPre.drop i).take 1 = [.atom a]) : Ev.atom a ∈ es := by
  rw [VerifySub.vs_body_eq] at hw
  exact atom_mem_walk vsPre_noRetS hw (mem_of_drop_take h)

theorem loadHolds_func {p v v' : E} {off : ℕ} (h : LoadHolds rd p off v) (h' : LoadHolds rd p off v') : v = v' :=
  Option.some.inj (h.2.symm.trans h'.2)

set_option maxHeartbeats 1000000 in
/-- **`verify_sub`'s values**, from its path within the honest pushes: the chunk count, the table logs (the
Keccak table's `τ` at least `9`, word `7` of its `kappa_base` buffer `v112`), the tallest log, the width
and the link's permutations. -/
theorem vs_node {s : NodeStatement} {w : NodeWitness} (hch : ChildrenOk guestBytecode guestSeed w) {σ : Val}
    (hp : PathIn coreProgram rd (Prover.honestPushes guestBytecode guestSeed s w) "verify_sub" σ) :
    VsNodeVals "verify_sub" σ ∧ (∃ τ, 9 ≤ τ ∧ τ ≤ 24 ∧ σ (.n 120) = gen ^ τ ∧ LoadHolds rd (σ (.n 112)) 7 (gen ^ τ)) ∧
      ∃ n, n ≤ 24 ∧ σ (.n 408) = gen ^ n := by
  obtain ⟨fn, hf, -, es, vs, hw, hes, hpops⟩ := hp
  rw [coreProgram_find?_at (j := idx% «verify_sub») rfl] at hf
  obtain rfl := Option.some.inj hf
  have hload : ∀ {i : ℕ} {a : Atom}, (VerifySub.vsPre.drop i).take 1 = [.atom a] → a.Holds rd σ :=
    fun h => hes _ (vs_atom hw h)
  -- the chunk count
  obtain ⟨n42, hn42, e42⟩ :=
    (proofVals_of hch (hpops _ (hint_stack_mem (rd := rd) (σ := σ) (vs_atom hw vsS24)))).chunks rfl
  have e42' : σ (.n 42) = Prover.count n42 := by
    simpa using e42
  -- the table logs
  obtain ⟨hs, ehs, hs24, hs9⟩ := (proofVals_of hch (hpops _ (hint_heap_mem (rd := rd) (σ := σ)
    (vs_atom hw vsS81)))).logs rfl
  have ehs' : (Dest.heap (.n 6) 0 6).words rd σ = hs.map Prover.count := ehs
  have hlen : hs.length = 6 := by
    have := congrArg List.length ehs'
    simp only [Dest.words, List.length_map, List.length_range] at this
    exact this.symm
  obtain ⟨a0, a1, a2, a3, a4, a5, rfl⟩ : ∃ a0 a1 a2 a3 a4 a5, hs = [a0, a1, a2, a3, a4, a5] := by
    match hs, hlen with
    | [a0, a1, a2, a3, a4, a5], _ => exact ⟨_, _, _, _, _, _, rfl⟩
  have h5 : a5 ≤ 24 := by simpa using hs24 5 (by omega)
  have h9 : 9 ≤ a5 := by simpa using hs9
  have w5 := heap_words_getD (rd := rd) (σ := σ) (p := .n 6) (off := 0) (len := 6) (k := 5) (v := σ (.n 120))
    (by norm_num) (hload vsS90)
  rw [ehs'] at w5
  simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero] at w5
  have g120 : GPow (σ (.n 120)) a5 := by rw [← w5]; exact count_gpow (by omega)
  -- the link's shape
  obtain ⟨n, wd, b, hn24, hw19, hw24, esh⟩ := (proofVals_of hch (hpops _ (hint_heap_mem (rd := rd) (σ := σ)
    (vs_atom hw vsS375)))).shape rfl
  have esh' : (Dest.heap (.n 9) 0 4).words rd σ =
      [Prover.count n, Prover.count wd, b, Prover.count ((packedChallenges tables n wd + 7) / 8)] := esh
  have rd0 := heap_words_getD (rd := rd) (σ := σ) (p := .n 9) (off := 0) (len := 4) (k := 0) (v := σ (.n 408))
    (by norm_num) (hload vsS376)
  have rd1 := heap_words_getD (rd := rd) (σ := σ) (p := .n 9) (off := 0) (len := 4) (k := 1) (v := σ (.n 409))
    (by norm_num) (hload vsS377)
  have rd3 := heap_words_getD (rd := rd) (σ := σ) (p := .n 9) (off := 0) (len := 4) (k := 3) (v := σ (.n 645))
    (by norm_num) (hload vsS537)
  rw [esh'] at rd0 rd1 rd3
  simp only [List.getD_cons_zero, List.getD_cons_succ] at rd0 rd1 rd3
  have hq := packed_le hn24 hw19 hw24
  have g408 : GPow (σ (.n 408)) n := by rw [← rd0]; exact count_gpow (by omega)
  have g409 : GPow (σ (.n 409)) wd := by rw [← rd1]; exact count_gpow (by omega)
  have g645 : GPow (σ (.n 645)) ((packedChallenges tables n wd + 7) / 8) := by
    rw [← rd3]; exact count_gpow (by omega)
  have g42 : GPow (σ (.n 42)) n42 := by rw [e42']; exact count_gpow (by omega)
  refine ⟨⟨fun _ => ⟨⟨n42, g42, hn42⟩, ?_, ?_, ?_, ?_⟩, fun h => absurd h (by decide),
    fun h => absurd h (by decide)⟩, ⟨a5, h9, h5, g120.1, ?_⟩, n, hn24, g408.1⟩
  · rw [g645.logG]; exact hq
  · rw [g409.logG]; exact hw24
  · rw [g408.logG]; exact hn24
  · rw [g120.logG]; exact h5
  · have l98 : LoadHolds rd (σ (.n 112)) 7 (σ (.n 120)) := hload vsS98
    rw [← g120.1]; exact l98

/-! ## Down the tree -/

/-- What `verify_sub` passes down: `verify_keccak`'s table log `τ ≥ 4`, `check_stack_terminal`'s kappas'
word `7` a power of `g` within `24`. -/
def VsDown (rd : Reader) (f : String) (args : List E) : Prop :=
  (f = "verify_keccak" → ∃ τ, 4 ≤ τ ∧ τ ≤ 24 ∧ args.getD 6 0 = gen ^ τ) ∧
  (f = "check_stack_terminal" → (∃ τ, τ ≤ 24 ∧ LoadHolds rd (args.getD 1 0) 7 (gen ^ τ)) ∧
    ∃ n, n ≤ 24 ∧ args.getD 6 0 = gen ^ n)

theorem vsPreIn {s : NodeStatement} {w : NodeWitness} (hch : ChildrenOk guestBytecode guestSeed w) :
    PreIn coreProgram rd (Prover.honestPushes guestBytecode guestSeed s w) (VsDown rd) := by
  intro f σ hp _ fn hf es vs hw c hc _
  have hsite : (c.f, c.args) ∈ Stmt.blockSitesH fn.body := by
    have := walk_sites (σ := σ) fn.body (c := c) (by rw [hw]; exact hc)
    exact this
  have hcb : c.f ∈ Stmt.blockCallees fn.body := walk_callees (σ := σ) fn.body (by rw [hw]; exact hc)
  by_cases hv : f = "verify_sub"
  · subst hv
    have hfn : fn = fn% «verify_sub» := Option.some.inj (hf.symm.trans (coreProgram_find?_at (j := idx% «verify_sub») rfl))
    subst hfn
    have hok := List.all_eq_true.mp vs_sites _ hsite
    simp only [vsSiteOk, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hok
    obtain ⟨-, ⟨τ, h9, h24, e120, l98⟩, n, hn, e408⟩ := vs_node hch hp
    refine ⟨fun hk => ⟨τ, by omega, h24, ?_⟩, fun hk => ?_⟩
    · have ha := hok.1.resolve_left (by simpa using hk)
      rw [ha]
      simpa [vkArgs] using e120
    · have ha := hok.2.resolve_left (by simpa using hk)
      have hl7 : (c.args.take 7).length = 7 := by rw [ha]; rfl
      match hca : c.args, ha, hl7 with
      | x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: rest, hxy, _ =>
        simp only [List.take_succ_cons, List.take_zero, List.cons.injEq, and_true] at hxy
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hxy
        exact ⟨⟨τ, h24, by simpa using l98⟩, n, hn, by simpa using e408⟩
      | [], _, h => simp at h
      | [_], _, h => simp at h
      | [_, _], _, h => simp at h
      | [_, _, _], _, h => simp at h
      | [_, _, _, _], _, h => simp at h
      | [_, _, _, _, _], _, h => simp at h
      | [_, _, _, _, _, _], _, h => simp at h
  · have hnot : c.f ≠ "verify_keccak" ∧ c.f ≠ "check_stack_terminal" := by
      rcases calleesVs_of_find hf c.f hcb with h | h | h
      · constructor <;> rintro e <;> rw [e] at h <;> exact h (by decide)
      · subst h
        have hfn : fn = coreProgram[Data.chidxLoop]'ch_nodeIdx.hl := Option.some.inj (hf.symm.trans loop_find)
        subst hfn
        have := List.all_eq_true.mp loop_callees _ hcb
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
        exact this
      · exact absurd h hv
    exact ⟨fun h => absurd h hnot.1, fun h => absurd h hnot.2⟩

/-! ## The callees' values -/

theorem winv4_mul : word 8070450532247928836 0 * gen ^ 4 = 1 := by
  rw [show gen ^ 4 = ofK (K.ofBits 16) by
      rw [← word_two_pow (a := 4) (by decide)]; exact word_eOfNat _,
    show word 8070450532247928836 0 = ofK (K.ofBits 8070450532247928836) from word_eOfNat _,
    ← ofK_mul, show K.ofBits 8070450532247928836 * K.ofBits 16 = 1 by decide +kernel, ofK_one]

theorem pow_mul_winv4 {t : ℕ} (h : 4 ≤ t) : gen ^ t * word 8070450532247928836 0 = gen ^ (t - 4) := by
  conv_lhs => rw [show t = (t - 4) + 4 by omega, pow_add, mul_assoc, mul_comm (gen ^ 4), winv4_mul, mul_one]

theorem vkS : ((fn% «verify_keccak»).body.take 7).drop 5 =
    [.atom (.const (.n 17) (word 8070450532247928836 0)), .atom (.mul (.n 18) (.n 6) (.n 17))] :=
  stmtsEqb_sound (by decide +kernel)

theorem vkS_noRet : Stmt.noRetListS ((fn% «verify_keccak»).body.take 7) = true := by decide +kernel

theorem cstS : ((fn% «check_stack_terminal»).body.take 36).drop 34 =
    [.atom (.const (.n 57) (word 64 0)), .atom (.mul (.n 58) (.n 51) (.n 57))] :=
  stmtsEqb_sound (by decide +kernel)

theorem cstS28 : (((fn% «check_stack_terminal»).body.take 36).drop 28).take 1 = [.atom (.load (.n 51) (.n 1) 7)] :=
  stmtsEqb_sound (by decide +kernel)

theorem cstS_noRet : Stmt.noRetListS ((fn% «check_stack_terminal»).body.take 36) = true := by decide +kernel

theorem vk_params : (fn% «verify_keccak»).params =
    [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11] := rfl

theorem cst_params2 : (fn% «check_stack_terminal»).params.take 2 = [.n 0, .n 1] := by decide +kernel

/-- **`verify_keccak`'s reduced height**, from its table log. -/
theorem vk_node {σ : Val} (hp : PathIn coreProgram rd H "verify_keccak" σ)
    (hpre : PreAt coreProgram (VsDown rd) "verify_keccak" σ) : VsNodeVals "verify_keccak" σ := by
  obtain ⟨fn, hf, -, es, vs, hw, hes, -⟩ := hp
  rw [coreProgram_find?_at (j := idx% «verify_keccak») rfl] at hf
  obtain rfl := Option.some.inj hf
  obtain ⟨τ, h4, h24, e6⟩ := (hpre _ (coreProgram_find?_at (j := idx% «verify_keccak») rfl)).1 rfl
  rw [vk_params] at e6
  simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero] at e6
  rw [← List.take_append_drop 7 (fn% «verify_keccak»).body] at hw
  have m17 : Stmt.atom (.const (.n 17) (word 8070450532247928836 0)) ∈ (fn% «verify_keccak»).body.take 7 :=
    mem_of_drop_eq vkS List.mem_cons_self
  have m18 : Stmt.atom (.mul (.n 18) (.n 6) (.n 17)) ∈ (fn% «verify_keccak»).body.take 7 :=
    mem_of_drop_eq vkS (List.mem_cons_of_mem _ List.mem_cons_self)
  have a17 : σ (.n 17) = word 8070450532247928836 0 := hes _ (atom_mem_walk vkS_noRet hw m17)
  have a18 : σ (.n 18) = σ (.n 6) * σ (.n 17) := hes _ (atom_mem_walk vkS_noRet hw m18)
  refine ⟨fun h => absurd h (by decide), fun _ => ⟨τ - 4, ⟨?_, by omega⟩, ?_⟩, fun h => absurd h (by decide)⟩
  · rw [a18, a17, e6, pow_mul_winv4 h4]
  · rw [e6, logG_gen_pow (e := τ) (by omega)]; omega

/-- **`check_stack_terminal`'s window**, from the kappas `verify_sub` wrote. -/
theorem cst_node {σ : Val} (hp : PathIn coreProgram rd H "check_stack_terminal" σ)
    (hpre : PreAt coreProgram (VsDown rd) "check_stack_terminal" σ) : VsNodeVals "check_stack_terminal" σ := by
  obtain ⟨fn, hf, -, es, vs, hw, hes, -⟩ := hp
  rw [coreProgram_find?_at (j := idx% «check_stack_terminal») rfl] at hf
  obtain rfl := Option.some.inj hf
  obtain ⟨⟨τ, h24, l⟩, -⟩ := (hpre _ (coreProgram_find?_at (j := idx% «check_stack_terminal») rfl)).2 rfl
  have e1 : ((fn% «check_stack_terminal»).params.map σ).getD 1 0 = σ (.n 1) := by
    rw [← List.take_append_drop 2 (fn% «check_stack_terminal»).params, cst_params2]; rfl
  rw [e1] at l
  rw [← List.take_append_drop 36 (fn% «check_stack_terminal»).body] at hw
  have m51 : Stmt.atom (.load (.n 51) (.n 1) 7) ∈ (fn% «check_stack_terminal»).body.take 36 :=
    mem_of_drop_take cstS28
  have m57 : Stmt.atom (.const (.n 57) (word 64 0)) ∈ (fn% «check_stack_terminal»).body.take 36 :=
    mem_of_drop_eq cstS List.mem_cons_self
  have m58 : Stmt.atom (.mul (.n 58) (.n 51) (.n 57)) ∈ (fn% «check_stack_terminal»).body.take 36 :=
    mem_of_drop_eq cstS (List.mem_cons_of_mem _ List.mem_cons_self)
  have a51 : LoadHolds rd (σ (.n 1)) 7 (σ (.n 51)) := hes _ (atom_mem_walk cstS_noRet hw m51)
  have a57 : σ (.n 57) = word 64 0 := hes _ (atom_mem_walk cstS_noRet hw m57)
  have a58 : σ (.n 58) = σ (.n 51) * σ (.n 57) := hes _ (atom_mem_walk cstS_noRet hw m58)
  have e51 : σ (.n 51) = gen ^ τ := loadHolds_func a51 l
  have e64 : word 64 0 = gen ^ 6 := by
    rw [show (64 : ℕ) = 2 ^ 6 by norm_num]; exact word_two_pow (by decide)
  refine ⟨fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ => ?_⟩
  rw [a58, a57, e51, e64, ← pow_add, logG_gen_pow (e := τ + 6) (by omega)]
  omega

/-! ## Every node -/

/-- **What `verify_sub` certifies, at every node of `main`'s honest tree.** -/
theorem vsVals (al : String → Bool) : VsVals al := by
  intro s w hrel hlim hch rd t h
  have hH : ∀ p ∈ t.pops coreProgram rd, p ∈ Prover.honestPushes guestBytecode guestSeed s w :=
    fun p hp => mem_of_sameStreams h.pops hp
  have hroot : VsDown rd t.name [] := by
    rw [h.name]; exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  refine (every_pathIn_preAt (vsPreIn hch) h.valid hH hroot).mono fun f σ ⟨hp, hpre⟩ => ?_
  by_cases h1 : f = "verify_sub"
  · subst h1; exact (vs_node hch hp).1
  by_cases h2 : f = "verify_keccak"
  · subst h2; exact vk_node hp hpre
  by_cases h3 : f = "check_stack_terminal"
  · subst h3; exact cst_node hp hpre
  exact ⟨fun h => absurd h h1, fun h => absurd h h2, fun h => absurd h h3⟩

/-- **`main`'s cycles** (`GuestLeft.cycles` for every allocator). -/
theorem mainCycles_all (al : String → Bool) : MainCycles al true := mainCycles_of_vs (vsVals al) (loopMeta_all al)

end
end LeanVM.Guest.Complete
