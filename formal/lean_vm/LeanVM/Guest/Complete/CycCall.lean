/-
  LeanVM.Guest.Complete.CycCall

  `main` enters the children's loop at counter `g^0` with end `g^n`, `n` its children, and only when `n > 0`
  (`mainLoopCall`).
-/

module

public import LeanVM.Guest.Complete.CycLoop

/-!
# `main`'s loop call

`main`'s only call of `__loop4_main` is `callIf v406 __loop4_main [v407, v6, ...]` (`main_loop_calls`, by the kernel
over its straight segments), with `v407 = 1`, `v406 = 1 + v6` and `v6` its children's count `g^n` (`main_meta`). A
valid callee is a taken call's (`kidsValid_mem_valid`), so `v406 ≠ 0`, `n > 0`, and its arguments start `[g^0, g^n]`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Guest.Budget LeanVM.Guest.Value

@[expose] public section

/-! ## Valid callees -/

variable {P : Core.Program} {rd : Reader}

/-- A valid tree's arguments are its function's parameters' values. -/
theorem valid_args_eq : ∀ {t : Tree} {a r a' r' : List E}, t.Valid P rd a r → t.Valid P rd a' r' → a = a'
  | .node f σ bufs kids, _, _, _, _, h, h' => by
      obtain ⟨fn, hf, hp, -⟩ := h
      obtain ⟨fn', hf', hp', -⟩ := h'
      rw [hf] at hf'
      cases hf'
      exact hp.symm.trans hp'
  | .phantom .., _, _, _, _, h, _ => h.elim

/-- **A valid callee is a taken call's.** -/
theorem kidsValid_mem_valid {σ : Val} : ∀ {cs : List Call} {ks : List Tree}, Tree.KidsValid P rd σ cs ks →
    ∀ k ∈ ks, ∀ {a r : List E}, k.Valid P rd a r →
      ∃ c ∈ cs, k.name = c.f ∧ c.taken = true ∧ k.Valid P rd (c.args.map σ) (c.rets.map σ)
  | [], [], _, k, hk, _, _, _ => (List.not_mem_nil hk).elim
  | [], _ :: _, h, _, _, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _, _, _ => h.elim
  | c :: cs, k' :: ks, ⟨hn, hc, hks⟩, k, hk, a, r, hv => by
      rcases List.mem_cons.mp hk with rfl | hk
      · by_cases ht : c.taken = true
        · rw [ite_eq_left ht] at hc
          exact ⟨c, List.mem_cons_self, hn, ht, hc⟩
        · rw [ite_eq_right ht] at hc
          obtain ⟨f, σ', rfl⟩ := hc.1
          exact hv.elim
      · obtain ⟨c', hc', h⟩ := kidsValid_mem_valid hks k hk hv
        exact ⟨c', List.mem_cons_of_mem _ hc', h⟩

/-! ## `main`'s calls of the loop -/

theorem calls_flatMap (σ : Val) : ∀ L : List Stmt, calls (L.flatMap (slEvs σ)) = L.flatMap fun s => calls (slEvs σ s)
  | [] => rfl
  | s :: L => by rw [List.flatMap_cons, calls_append, calls_flatMap σ L, List.flatMap_cons]

/-- A statement calling the loop only as `callIf v406 __loop4_main [v407, v6, ...]`. -/
def loopCallOk : Stmt → Bool
  | .callIf c f args => f != "__loop4_main" || (c == .n 406 && args.take 2 == [.n 407, .n 6])
  | .call f _ _ => f != "__loop4_main"
  | _ => true

theorem loopCallOk_calls (σ : Val) {s : Stmt} (h : loopCallOk s = true) :
    ∀ c ∈ calls (slEvs σ s), c.f = "__loop4_main" → c.args.take 2 = [.n 407, .n 6] ∧
      (c.taken = true → σ (.n 406) ≠ 0) := by
  intro c hc hf
  cases s with
  | atom a => simp [slEvs, calls, Ev.call?] at hc
  | call f args rets =>
      simp only [slEvs] at hc
      have e : calls [Ev.call f args rets] = [⟨f, args, rets, true⟩] := rfl
      rw [e, List.mem_singleton] at hc
      subst hc
      simp only [loopCallOk, bne_iff_ne, ne_eq] at h
      exact absurd hf h
  | callIf c' f args =>
      simp only [slEvs] at hc
      have e : calls [Ev.inK c', if σ c' = 0 then .skip f args else .call f args []] =
          [⟨f, args, [], !decide (σ c' = 0)⟩] := by
        by_cases h0 : σ c' = 0 <;> simp only [h0, ↓reduceIte, decide_true, decide_false, Bool.not_true,
          Bool.not_false] <;> rfl
      rw [e, List.mem_singleton] at hc
      subst hc
      simp only [loopCallOk, Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with h | ⟨rfl, ha⟩
      · exact absurd hf h
      · refine ⟨ha, fun ht => ?_⟩
        simpa using ht
  | _ => simp [slEvs, calls] at hc

set_option maxRecDepth 200000 in
theorem main_loopCallOk : (Main.mPre ++ Main.mDa ++ Main.mDaZ ++ Main.mMid ++ Main.mLeaf ++ Main.mAgg ++
    Main.mPost).all loopCallOk = true := by
  decide +kernel

/-- **`main`'s calls of the loop**: arguments `[v407, v6, ...]`, taken only when `v406 ≠ 0`. -/
theorem main_loop_calls (σ : Val) : ∀ c ∈ calls (mainEvs σ), c.f = "__loop4_main" →
    c.args.take 2 = [.n 407, .n 6] ∧ (c.taken = true → σ (.n 406) ≠ 0) := by
  intro c hc hf
  have hall := main_loopCallOk
  simp only [List.all_append, Bool.and_eq_true] at hall
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hall
  have key : ∀ L : List Stmt, L.all loopCallOk = true → c ∈ calls (L.flatMap (slEvs σ)) →
      c.args.take 2 = [.n 407, .n 6] ∧ (c.taken = true → σ (.n 406) ≠ 0) := by
    intro L hL hcL
    rw [calls_flatMap, List.mem_flatMap] at hcL
    obtain ⟨s, hs, hcs⟩ := hcL
    exact loopCallOk_calls σ (List.all_eq_true.mp hL s hs) c hcs hf
  have hinK : ∀ (v : V) (L : List Stmt), calls (Ev.inK v :: L.flatMap (slEvs σ)) = calls (L.flatMap (slEvs σ)) :=
    fun _ _ => rfl
  unfold mainEvs at hc
  simp only [calls_append, List.mem_append, hinK] at hc
  rcases hc with (((hc | hc) | hc) | hc) | hc
  · exact key _ h1 hc
  · by_cases ha : σ (.n 384) = 0
    · rw [ite_eq_left ha] at hc; exact key _ h2 hc
    · rw [ite_eq_right ha] at hc; exact key _ h3 hc
  · exact key _ h4 hc
  · by_cases hb : σ (.n 423) = 0
    · rw [ite_eq_left hb] at hc; exact key _ h5 hc
    · rw [ite_eq_right hb] at hc; exact key _ h6 hc
  · exact key _ h7 hc

set_option maxRecDepth 200000 in
theorem main_mid_atoms : Atom.const (.n 407) (word 1 0) ∈ VsC.atomsOf Main.mMid ∧
    Atom.const (.n 405) (word 1 0) ∈ VsC.atomsOf Main.mMid ∧ Atom.add (.n 406) (.n 405) (.n 6) ∈ VsC.atomsOf Main.mMid := by
  decide +kernel

/-- **`main` enters the loop at `g^0` with end `g^n`, `n > 0` its children.** -/
theorem mainLoopCall (al : String → Bool) : MainLoopCall al := by
  intro s w hrel hlim hch rd σ bufs kids h k hk hkn a r hkv
  have hm := main_meta h
  simp only [metaCells, List.cons.injEq, and_true] at hm
  obtain ⟨-, -, -, -, -, -, h6, -⟩ := hm
  have hb := hlim.withinMemoryBudget
  simp only [NodeWitness.memoryBudget, NodeWitness.childClaimCount] at hb
  have g6 : GPow (σ (.n 6)) w.children.length := h6 ▸ count_gpow (by omega)
  obtain ⟨fn, hf, -, es, vs, hw, -, hes, hks⟩ := h.valid
  rw [Main.find_main] at hf
  obtain rfl := Option.some.inj hf
  rw [walk_main] at hw
  obtain ⟨rfl, -⟩ := Out.ret.inj hw
  obtain ⟨c, hc, hcn, hct, hcv⟩ := kidsValid_mem_valid hks k hk hkv
  obtain ⟨hargs, htk⟩ := main_loop_calls σ c hc (hcn.symm.trans hkn)
  have h406 := htk hct
  have hin : ∀ x, x ∈ VsC.atomsOf Main.mMid → Ev.atom x ∈ mainEvs σ := fun x hx => by
    unfold mainEvs
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨_, atom_mem_of_atomsOf hx, by simp [slEvs]⟩)))
  obtain ⟨m407, m405, m406⟩ := main_mid_atoms
  have e407 : σ (.n 407) = word 1 0 := hes _ (hin _ m407)
  have e405 : σ (.n 405) = word 1 0 := hes _ (hin _ m405)
  have e406 : σ (.n 406) = σ (.n 405) + σ (.n 6) := hes _ (hin _ m406)
  rw [B1.word_one] at e407 e405
  have hlen : (itemsOf s w).children.length = w.children.length := by
    simp only [itemsOf, NodeItems.ofWitness, List.length_map]
  rw [hlen]
  have h0 : 0 < w.children.length := by
    rcases Nat.eq_zero_or_pos w.children.length with hz | hz
    · exfalso
      apply h406
      rw [e406, e405, g6.1, hz, pow_zero]
      exact CharTwo.add_self_eq_zero 1
    · exact hz
  refine ⟨?_, h0⟩
  rw [valid_args_eq hkv hcv]
  match hca : c.args, hargs with
  | x :: y :: rest, hxy =>
      simp only [List.take_succ_cons, List.take_zero, List.cons.injEq, and_true] at hxy
      obtain ⟨rfl, rfl⟩ := hxy
      simp only [List.map_cons, List.take_succ_cons, List.take_zero, e407, g6.1, pow_zero]
  | [x], hxy => simp at hxy
  | [], hxy => simp at hxy

end
end LeanVM.Guest.Complete
