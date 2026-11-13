module

public import LeanVM.Guest.Mode.Step

/-!
# Taken jumps

`jumpI_cases`: what the walk accepts as a taken `JUMP` (`JumpK`): a return, a jump in its own frame
to a later offset, to a jump table's arms or to the halting pc, a loop's tail call, or a call.
`jump_in`: a jump in the own frame the walk accepts goes, in the executor, to an offset it names, in
the same frame (`main`'s frame being `0`).
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-- Frame cell `f` holds the own frame's address. -/
def SelfF (F : Fun) (A : Abs) (f : ℕ) : Prop :=
  A.mono f = some ⟨1, 0, []⟩ ∨ (A.mono f = some ⟨0, 0, []⟩ ∧ F.main = true)

/-- The kinds of taken jumps the walk accepts, with where they go and the state after. -/
inductive JumpK (E : Env) (F : Fun) (i : ℕ) (A : Abs) (d f : ℕ) : Go → Abs → Prop
  | ret : d = 0 → f = 1 → retOk A F.sig = true → JumpK E F i A d f .out A
  | fwd (e : ℕ) : SelfF F A f → A.mono d = some ⟨0, e, []⟩ → F.entry + i < e → e < F.entry + F.len →
      JumpK E F i A d f (.to [e - F.entry]) A
  | halt : SelfF F A f → A.mono d = some ⟨0, E.halt, []⟩ → F.main = true → JumpK E F i A d f .out A
  | arms (ts : List ℕ) : SelfF F A f → armsOf E F A i d = some ts → JumpK E F i A d f (.to ts) A
  | tail (e : ℕ) (G : Sig) : A.mono f = some ⟨1, e, []⟩ → A.mono d = some ⟨0, F.entry, []⟩ →
      E.sigs.get F.entry = some G → tailOk A e G = true → loopOk A F.sig = true →
      JumpK E F i A d f .out A
  | call (mq : Mono) (r : ℕ) (G : Sig) (Gs : List Sig) : ¬SelfF F A f → A.mono f = some mq →
      A.hvGet (mq.shift 1) = some (.m ⟨1, 0, []⟩) → A.hvGet (mq.shift 0) = some (.m ⟨0, r, []⟩) →
      calleesOf E F A i d = some (G :: Gs) →
      (∀ G' ∈ G :: Gs, entryOk (foldlA (fun A G ↦ atCall A mq G) A (G :: Gs)) mq G' = true) →
      F.entry + i < r → r < F.entry + F.len →
      JumpK E F i A d f (.to [r - F.entry])
        (foldlA (fun B G' ↦ B.interS (afterCall (foldlA (fun A G ↦ atCall A mq G) A (G :: Gs)) mq G'))
          (afterCall (foldlA (fun A G ↦ atCall A mq G) A (G :: Gs)) mq G) Gs)

/-- **What a taken jump the walk accepts is.** -/
theorem jumpI_cases {E : Env} {F : Fun} {i : ℕ} {A : Abs} {d f : ℕ} {go : Go} {A' : Abs}
    (h : jumpI E F i A d f = some (go, A')) : JumpK E F i A d f go A' := by
  unfold jumpI at h
  by_cases hr : (d == 0 && f == 1) = true
  · rw [ite_eq_left hr] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at hr
    split_ifs at h with hok
    cases h
    exact .ret hr.1 hr.2 hok
  rw [ite_eq_right hr] at h
  dsimp only at h
  split_ifs at h with hself
  · have hS : SelfF F A f := by
      split at hself
      · rename_i hm; exact Or.inl hm
      · rename_i hm; exact Or.inr ⟨hm, hself⟩
      · cases hself
    split at h
    · rename_i e hd
      split_ifs at h with h1 h2
      · cases h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
        exact .fwd e hS hd h1.1 h1.2
      · cases h
        simp only [Bool.and_eq_true, beq_iff_eq] at h2
        rw [h2.2] at hd
        exact .halt hS hd h2.1
    · obtain ⟨ts, hts, h⟩ := Option.map_eq_some_iff.mp h
      cases h
      exact .arms ts hS hts
  · split at h
    · rename_i e hf
      split at h
      · rename_i t hd
        split at h
        · rename_i G hG
          split_ifs at h with h1
          cases h
          simp only [Bool.and_eq_true, beq_iff_eq] at h1
          obtain ⟨⟨rfl, h2⟩, h3⟩ := h1
          exact .tail e G hf hd hG h2 h3
        · cases h
      · cases h
    · rename_i mq _ hf
      split at h
      · rename_i r h1 h0
        split at h
        · rename_i G Gs hc
          split_ifs at h with h2
          cases h
          simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h2
          refine .call mq r G Gs (fun hS ↦ hself ?_) hf h1 h0 hc h2.1.1 h2.1.2 h2.2
          rcases hS with hm | ⟨hm, hmain⟩
          · rw [hm]; rfl
          · rw [hm]; exact hmain
        · cases h
      · cases h
    · cases h

/-! ## Jumps in the own frame -/

theorem mapOpt_mem {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (acc ys : List β),
      List.rec (motive := fun _ ↦ List β → Option (List β)) (fun acc ↦ some acc.reverse)
        (fun x _ ih acc ↦ match f x with
          | some y => ih (y :: acc)
          | none => none) l acc = some ys →
      ∀ x ∈ l, ∃ y ∈ ys, f x = some y
  | [], _, _, _, x, hx => absurd hx List.not_mem_nil
  | a :: l, acc, ys, h, x, hx => by
    simp only at h
    split at h
    · rename_i y hy
      rcases List.mem_cons.mp hx with rfl | hx
      · refine ⟨y, ?_, hy⟩
        have key : ∀ (l : List α) (acc ys : List β), y ∈ acc →
            List.rec (motive := fun _ ↦ List β → Option (List β)) (fun acc ↦ some acc.reverse)
              (fun x _ ih acc ↦ match f x with
                | some y => ih (y :: acc)
                | none => none) l acc = some ys → y ∈ ys := by
          intro l
          induction l with
          | nil => intro acc ys hm h; cases h; exact List.mem_reverse.mpr hm
          | cons b l ih =>
            intro acc ys hm h
            simp only at h
            split at h
            · exact ih _ _ (List.mem_cons_of_mem _ hm) h
            · cases h
        exact key l (y :: acc) ys (List.mem_cons_self ..) h
      · exact mapOpt_mem f l (y :: acc) ys h x hx
    · cases h

theorem mem_mapOpt {α β : Type} {f : α → Option β} {l : List α} {ys : List β}
    (h : mapOpt f l = some ys) {x : α} (hx : x ∈ l) : ∃ y ∈ ys, f x = some y :=
  mapOpt_mem f l [] ys h x hx

/-- The word of frame cell `o` known as `fp^p·g^k`, naming `x`. -/
theorem mono_pow {s : St} {A : Abs} (hA : Holds s A) {o p k x : ℕ}
    (hm : A.mono o = some ⟨p, k, []⟩) (hv : s.mem.get (s.fp + o) = some (ofK (g ^ x))) :
    g ^ x = g ^ (s.fp * p + k) := by
  obtain ⟨u, hu, hmu⟩ := hA.mono_val hm (written_of_get hv)
  rw [hv] at hu
  cases hu
  exact ofK_injective (pow_val' hmu)

/-- A jump the walk knows to stay in the frame does. -/
theorem selfF_fp {s : St} {A : Abs} {F : Fun} {f x : ℕ} (hA : Holds s A) (hS : SelfF F A f)
    (hfp : s.fp < maxCells) (hx : x < maxCells) (hv : s.mem.get (s.fp + f) = some (ofK (g ^ x))) :
    x = s.fp ∨ (F.main = true ∧ x = 0) := by
  rcases hS with hm | ⟨hm, hmain⟩
  · have := mono_pow hA hm hv
    rw [Nat.mul_one, Nat.add_zero] at this
    exact Or.inl (gpow_inj (by unfold maxCells at hx; omega) (by unfold maxCells at hfp; omega) this)
  · have := mono_pow hA hm hv
    rw [Nat.mul_zero, Nat.add_zero, pow_zero] at this
    exact Or.inr ⟨hmain, gpow_inj (by unfold maxCells at hx; omega) (by norm_num)
      (this.trans (pow_zero g).symm)⟩

/-- **A jump to arms or a later offset** goes, in the executor, to a pc of the function at an offset
the walk names. -/
theorem jump_to_pc {En : Env} {F : Fun} {i : ℕ} {A : Abs} {d f : ℕ} {ts : List ℕ} {A' : Abs}
    {s : St} (hA : Holds s A) (hE : EnvOk s En) (hk : JumpK En F i A d f (.to ts) A') (hS : SelfF F A f)
    {pc : ℕ} (hpc : pc < 2 ^ 62) (hlen : F.entry + F.len < 2 ^ 62)
    (hv : s.mem.get (s.fp + d) = some (ofK (g ^ pc))) :
    ∃ j ∈ ts, pc = F.entry + j ∧ j < F.len := by
  cases hk with
  | fwd e _ hd h1 h2 =>
    have := mono_pow hA hd hv
    rw [Nat.mul_zero, Nat.zero_add] at this
    obtain rfl := gpow_inj (by omega) (by omega) this
    exact ⟨pc - F.entry, List.mem_singleton_self _, by omega, by omega⟩
  | call _ _ _ _ hn => exact absurd hS hn
  | arms ts' _ hts =>
    unfold armsOf at hts
    split at hts
    · rename_i x d0 n htab hn
      split_ifs at hts with hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨hlt, hlo⟩, hhi⟩ := hc
      obtain ⟨X, hX, hXn⟩ := Abs.ltI_sound hA hlt (show IdxVal s (.num n) n from rfl)
      obtain ⟨vx, ex, hbx, rfl, hex, rfl⟩ := hX
      obtain ⟨u, hu, c, cc, hmc, hnc, hgc⟩ := hA.v d _ htab
      rw [hv] at hu
      cases hu
      obtain ⟨p, hp, rfl⟩ := MonoVal.base1.mp hmc
      obtain rfl := hbx.unique hp
      rw [← ofK_mul, ← pow_add] at hnc
      obtain rfl := names_ofK (by have := hE.2.1; unfold maxCells at this; omega) hnc
      obtain ⟨y, hy, hfy⟩ := mem_mapOpt hts (List.mem_range.mpr (show X + 0 < n by omega))
      rw [Nat.add_zero] at hfy
      obtain ⟨tgt, htgt, hfy⟩ := Option.bind_eq_some_iff.mp hfy
      split_ifs at hfy with hb
      cases hfy
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      have hcell := hE.2.2 (d0 + X) tgt (by omega) (by omega) htgt
      rw [hgc] at hcell
      have := ofK_injective (Option.some.inj hcell)
      obtain rfl := gpow_inj (by omega) (by omega) this
      exact ⟨_, hy, by omega, by omega⟩
    · cases hts

end

end LeanVM.Guest.Mode
