/-
  LeanVM.Guest.Backend.Sound.Obl.Lq

  The obligations of `level_queries`' specializations: their call of `opening_queries` gets the
  walk's precondition from their own, with `N` set to `g^n`.
-/

module

public import LeanVM.Guest.Backend.Sound.Obl.GuestU

/-!
# `level_queries`

`level_queries__L{n}_…` (six parameters) sets `σ 12 = g^n` at statement `7` and calls its
`opening_queries` specialization at statement `8` on `[…, win_ptrs, σ 12]`, `win_ptrs` its
argument `5`. Its precondition (`XSpec.lq n w`) is `OqMainWins` on `win_ptrs` at `g^n`, which is
the callee's (`XSpec.main w`) on its arguments `6` and `7`. `lqOk` decides the shape, `lq_obl`
gives `OblFn`.
-/

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Protocol.Verifier LeanVM.Guest.Value

@[expose] public section

/-- The call of the walk at statement `8` and its count `g^n` at statement `7`. -/
def lqCallOk (n : ℕ) (main : String) : List Stmt → Bool
  | .atom (.const (.n 12) c) :: .call f args _ :: _ =>
      decide (f = main) && decide (8 ≤ args.length) && decide (args.getD 6 default = .n 5) &&
        decide (args.getD 7 default = .n 12) &&
        (match lowBits c with
          | some a => decide (K.ofBits a = addressOfIndex n)
          | none => false)
  | _ => false

/-- **A `level_queries` specialization's decided check**: function `j` is named `name`, has six
parameters, its table entry is `lq n w` and its callee's `main w`, it sets `g^n` and calls the
walk returning nowhere before, and the analysis accepts it with the call as a site. -/
def lqOkF (g : Fn) (name main : String) : Bool :=
  match xSpecOf name with
  | some (.lq n w) =>
      decide (g.name = name) && decide (g.params = (List.range 6).map V.n) &&
        (guestTab.sig name).ext && decide (xSpecOf main = some (.main w)) &&
        Stmt.noRetList (g.body.take 8) && lqCallOk n main (g.body.drop 7) &&
        chkFnX guestTab [] [8] g
  | _ => false

/-- `lqOkF` of function `j`. -/
noncomputable def lqOk (j : ℕ) (name main : String) : Bool :=
  lqOkF (coreProgram.getD j default) name main

theorem lqCallOk_spec {n : ℕ} {main : String} {l : List Stmt} (h : lqCallOk n main l = true) :
    ∃ c args rets r, l = .atom (.const (.n 12) c) :: .call main args rets :: r ∧
      8 ≤ args.length ∧ args.getD 6 default = .n 5 ∧ args.getD 7 default = .n 12 ∧
      c = gen ^ n := by
  unfold lqCallOk at h
  split at h
  · rename_i c f args rets r
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨rfl, hlen⟩, h6⟩, h7⟩, hc⟩ := h
    refine ⟨c, args, rets, r, rfl, hlen, h6, h7, ?_⟩
    split at hc
    · rename_i a ha
      simp only [decide_eq_true_eq] at hc
      rw [lowBits_spec ha, hc, ← gen_pow_eq_ofK]
    · exact absurd hc (by simp)
  · exact absurd h (by simp)

/-- **A `level_queries` specialization's obligations**, from its decided check. -/
theorem lq_obl {j : ℕ} {name main : String} (hok : lqOk j name main = true) :
    OblFn (coreProgram.getD j default) := by
  unfold lqOk lqOkF at hok
  split at hok
  case h_2 => exact absurd hok (by simp)
  rename_i n w hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨hn, hp⟩, he⟩, hxm⟩, hnr⟩, hcall⟩, hc⟩ := hok
  obtain ⟨c, args, rets, r8, h7, hlen, h6, h7', hcv⟩ := lqCallOk_spec hcall
  apply oblFn_of_chkX hc (fun _ _ _ _ _ _ _ p hp => absurd hp List.not_mem_nil)
  intro κ L _ _ C σ _ hpre i hi st ss hd hl
  simp only [List.mem_singleton] at hi
  subst hi
  have own := own_spec hpre (by rw [hn]; exact he) (by rw [hn]; exact hx)
  rw [hp] at own
  simp only [XSpec.Holds, getD_range_map (by norm_num : 5 < 6)] at own
  have h8 : (coreProgram.getD j default).body.drop 8 = .call main args rets :: r8 := by
    rw [show 8 = 7 + 1 from rfl, ← List.drop_drop, h7, List.drop_one, List.tail_cons]
  rw [h8] at hd
  obtain ⟨rfl, -⟩ := List.cons.inj hd
  have hk := holds_at (by norm_num : 7 < 8) hnr h7 hl
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hk
  intro _ sp hsp
  rw [hxm] at hsp
  obtain rfl := (Option.some.inj hsp).symm
  simp only [XSpec.Holds]
  rw [getD_map_lt (by omega), getD_map_lt (by omega), h6, h7', hk, hcv]
  exact own

end
end LeanVM.Guest.Backend.Obl
