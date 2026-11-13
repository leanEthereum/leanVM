module

public import LeanVM.Guest.Mode.Jump

/-!
# Calls and returns, in the executor

`call_enter`: a call the walk accepts (`JumpK.call`) enters, in the executor, a callee whose
signature is one of the call's, in a frame the caller's product names (`Frames`), its header naming
the caller's return pc and frame, and the callee's walk starts from a state that holds there, given
the callees' termination facts and the jump table's run. `ret_regs`: a return from a frame whose
header names `r` and `fp` goes there. `ret_resume`: the callee's guarantees at its return give the
state the caller's walk goes on from.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-- The program's pcs are small: its signatures' and its jump table's. -/
def EnvSmall (En : Env) : Prop :=
  (∀ t G, En.sigs.get t = some G → t < 2 ^ 62) ∧ ∀ d e, En.jt.get d = some e → e < 2 ^ 62

/-- The callee a call enters: one of its signatures, at the pc the executor goes to. -/
theorem callee_of {En : Env} {F : Fun} {i : ℕ} {A : Abs} {d : ℕ} {Gs : List Sig} {s : St} {pc : ℕ}
    (hA : Holds s A) (hE : EnvOk s En) (hS : EnvSmall En) (hc : calleesOf En F A i d = some Gs)
    (hpc : pc < 2 ^ 62) (hv : s.mem.get (s.fp + d) = some (ofK (g ^ pc))) :
    ∃ G ∈ Gs, En.sigs.get pc = some G := by
  unfold calleesOf at hc
  split at hc
  · rename_i e hd
    obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.mp hc
    obtain ⟨u, hu, hok⟩ := hA.v d _ hd
    rw [hv] at hu
    cases hu
    have he := hS.1 e G hG
    obtain rfl := gpow_inj (by omega) (by omega) (ofK_injective (pow_val hok))
    exact ⟨G, List.mem_singleton_self _, hG⟩
  · rename_i x d0 htab
    split at hc
    · rename_i n hn
      split_ifs at hc with hcnd
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcnd
      obtain ⟨⟨hlt, hlo⟩, hhi⟩ := hcnd
      obtain ⟨X, hX, hXn⟩ := Abs.ltI_sound hA hlt (show IdxVal s (.num n) n from rfl)
      obtain ⟨vx, ex, hbx, rfl, hex, rfl⟩ := hX
      obtain ⟨u, hu, c, cc, hmc, hnc, hgc⟩ := hA.v d _ htab
      rw [hv] at hu
      cases hu
      obtain ⟨p, hp, rfl⟩ := MonoVal.base1.mp hmc
      obtain rfl := hbx.unique hp
      rw [← ofK_mul, ← pow_add] at hnc
      obtain rfl := names_ofK (by have := hE.2.1; unfold maxCells at this; omega) hnc
      obtain ⟨G, hG, hfy⟩ := mem_mapOpt hc (List.mem_range.mpr (show X + 0 < n by omega))
      rw [Nat.add_zero] at hfy
      obtain ⟨tgt, htgt, hsig⟩ := Option.bind_eq_some_iff.mp hfy
      have hcell := hE.2.2 (d0 + X) tgt (by omega) (by omega) htgt
      rw [hgc] at hcell
      have ht := hS.2 _ _ htgt
      obtain rfl := gpow_inj (by omega) (by omega) (ofK_injective (Option.some.inj hcell))
      exact ⟨G, hG, hsig⟩
    · cases hc
  · cases hc

/-- The caller's state at a callee's: its memory, its frame. -/
def callerAt (sE : St) (fp : ℕ) : St := { sE with fp := fp }

theorem foldl_atCall_sound {sC sE : St} {mq : Mono} (F : Frames sC sE mq) :
    ∀ (Gs : List Sig) {A : Abs}, Holds sC A → (∀ G ∈ Gs, ∀ p ∈ G.term, LTF sE p.1 p.2) →
      Holds sC (foldlA (fun A G ↦ atCall A mq G) A Gs) := by
  intro Gs A hA hT
  rw [foldlA_eq]
  induction Gs generalizing A with
  | nil => exact hA
  | cons G Gs ih =>
    rw [List.foldl_cons]
    exact ih (atCall_sound F hA (hT G (List.mem_cons_self ..)))
      fun G' hG' ↦ hT G' (List.mem_cons_of_mem _ hG')

/-- **A call's entry**: the executor's state `sE` after the call's `JUMP` from `s` is the entry of a
callee among the call's, its frame named by the caller's product, its header naming the caller's
return pc and frame; its walk's entry state holds there, and the caller's state after the
callees' termination facts holds of the caller's frame. -/
theorem call_enter {En : Env} {F : Fun} {i : ℕ} {A : Abs} {d f : ℕ} {mq : Mono} {r : ℕ} {G : Sig}
    {Gs : List Sig} {s sE : St} (hA : Holds s A) (hE : EnvOk s En) (hS : EnvSmall En)
    (hfm : A.mono f = some mq) (h1 : A.hvGet (mq.shift 1) = some (.m ⟨1, 0, []⟩))
    (h0 : A.hvGet (mq.shift 0) = some (.m ⟨0, r, []⟩)) (hc : calleesOf En F A i d = some (G :: Gs))
    (hok : ∀ G' ∈ G :: Gs, entryOk (foldlA (fun A G ↦ atCall A mq G) A (G :: Gs)) mq G' = true)
    (hfp : s.fp < maxCells) (hle : s.mem ≤ sE.mem) (hwf : sE.mem.WF) (hu : sE.mem.used ≤ maxCells)
    (hfpE : sE.fp < maxCells) (hpcE : sE.pc < 2 ^ 62)
    (hd : s.mem.get (s.fp + d) = some (ofK (g ^ sE.pc)))
    (hf : s.mem.get (s.fp + f) = some (ofK (g ^ sE.fp)))
    (hT : ∀ G' ∈ G :: Gs, ∀ p ∈ G'.term, LTF sE p.1 p.2) (hjt : RW sE (jtRng En)) :
    Frames (callerAt sE s.fp) sE mq ∧
      Holds (callerAt sE s.fp) (foldlA (fun A G ↦ atCall A mq G) A (G :: Gs)) ∧
      sE.mem.get (sE.fp + 1) = some (ofK (g ^ s.fp)) ∧ sE.mem.get (sE.fp + 0) = some (ofK (g ^ r)) ∧
      ∃ G' ∈ G :: Gs, En.sigs.get sE.pc = some G' ∧ Holds sE (entryAbs En G') := by
  have hAC : Holds (callerAt sE s.fp) A := Holds.mono (s' := callerAt sE s.fp) hle rfl hA
  obtain ⟨u, hu, hmu⟩ := hA.mono_val hfm (written_of_get hf)
  rw [hf] at hu
  cases hu
  have Fr : Frames (callerAt sE s.fp) sE mq := ⟨rfl, MonoVal.mono (s' := callerAt sE s.fp) hle rfl hmu, hfpE, hfp, hwf, hu⟩
  have hA1 := foldl_atCall_sound Fr (G :: Gs) hAC hT
  obtain ⟨w1, hw1, hm1⟩ := hvGet_cell Fr hAC (by norm_num) h1
  obtain ⟨w0, hw0, hm0⟩ := hvGet_cell Fr hAC (by norm_num) h0
  have e1 : w1 = ofK (g ^ s.fp) := by
    have := pow_val' hm1
    rw [Nat.mul_one, Nat.add_zero] at this
    exact this
  have e0 : w0 = ofK (g ^ r) := pow_val hm0
  obtain ⟨G', hG', hsig⟩ := callee_of hA hE hS hc hpcE hd
  exact ⟨Fr, hA1, e1 ▸ hw1, e0 ▸ hw0, G', hG', hsig,
    entryOk_sound Fr hA1 (hok G' hG') hjt (hT G' hG')⟩

/-- **A return's registers**: a frame whose header names `r` and `fp` returns there. -/
theorem ret_regs {s s' : St} {r fp : ℕ} (hr : r < 2 ^ 62) (hfp : fp < maxCells)
    (h0 : s.mem.get (s.fp + 0) = some (ofK (g ^ r))) (h1 : s.mem.get (s.fp + 1) = some (ofK (g ^ fp)))
    (hpc' : s'.pc < 2 ^ 62) (hfp' : s'.fp < maxCells)
    (hd : s.mem.get (s.fp + 0) = some (ofK (g ^ s'.pc)))
    (hf : s.mem.get (s.fp + 1) = some (ofK (g ^ s'.fp))) : s'.pc = r ∧ s'.fp = fp := by
  rw [h0] at hd
  rw [h1] at hf
  exact ⟨gpow_inj (by omega) (by omega) (ofK_injective (Option.some.inj hd)).symm,
    gpow_inj (by unfold maxCells at hfp'; omega) (by unfold maxCells at hfp; omega)
      (ofK_injective (Option.some.inj hf)).symm⟩

/-- **After a return**: the callee's guarantees at its return give the state the caller's walk goes
on from. -/
theorem ret_resume {sC sR : St} {A1 : Abs} {mq : Mono} {G : Sig} {Gs : List Sig} {G' : Sig}
    (hG' : G' ∈ G :: Gs) (F : Frames sC sR mq) (hA : Holds sC A1) (hR : RetHolds sR G')
    (hL : ∀ r ∈ G'.postL, RW sR r) (hLP : ∀ q ∈ G'.postLP, PW sR q.1 q.2)
    (hT : ∀ p ∈ G'.term, LTF sR p.1 p.2) :
    Holds sC (foldlA (fun B G' ↦ B.interS (afterCall A1 mq G')) (afterCall A1 mq G) Gs) := by
  have hX := afterCall_sound F hA hR hL hLP hT
  rw [foldlA_eq]
  have e : Gs.foldl (fun B G' ↦ B.interS (afterCall A1 mq G')) (afterCall A1 mq G) =
      (Gs.map (afterCall A1 mq)).foldl Abs.inter (afterCall A1 mq G) := by
    rw [List.foldl_map]
    exact congrArg (fun f ↦ Gs.foldl f (afterCall A1 mq G))
      (funext fun B ↦ funext fun G' ↦ Abs.interS_eq _ _)
  rw [e]
  refine Holds.foldl_inter ?_ hX
  rcases List.mem_cons.mp hG' with rfl | h
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (List.mem_map_of_mem h)

end

end LeanVM.Guest.Mode
