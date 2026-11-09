/-
  LeanVM.Guest.B1.Place.OsBos

  open_stacked's frame-size bound: its frame, its buffers, a bound per callee.
-/

module

public import LeanVM.Guest.B1.Place.OsFinalK

/-!
# The frame-size bound

`osCallB fs Bk f`: a call of `f`, entered within `Bk f` words or skipped (its frame `fs f`).
`osKidsB fs Bk c`: the body's calls' total, one `osCallB` per call statement, whatever `σ` (a
call's callee is its statement's). `osBos fs Bk name c`: the frame `fs name`, the buffers, the
callees.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-- A call of `f`: entered within `Bk f` words, or skipped. -/
def osCallB (fs Bk : String → ℕ) (f : String) : ℕ := max (fs f) (Bk f)

/-- The body's callees' total, one `osCallB` per call statement. -/
def osKidsB (fs Bk : String → ℕ) (c : OsCfg) : ℕ :=
  (((osBodyA c).filterMap Main.Stmt.callS).map fun x ↦ osCallB fs Bk x.2.1).sum

/-- **`open_stacked`'s frame-size bound** at a configuration. -/
def osBos (fs Bk : String → ℕ) (name : String) (c : OsCfg) : ℕ :=
  fs name + (osSizesL c).sum + osKidsB fs Bk c

theorem mkCall_f (σ : Val) (x : Option V × String × List V × List V) :
    (Main.mkCall σ x).f = x.2.1 := by
  obtain ⟨cv, f, a, r⟩ := x; cases cv <;> rfl

theorem mkCalls_sumB (fs Bk : String → ℕ) (σ : Val) :
    ∀ xs : List (Option V × String × List V × List V),
      ((xs.map (Main.mkCall σ)).map fun c' ↦ osCallB fs Bk c'.f).sum =
        (xs.map fun x ↦ osCallB fs Bk x.2.1).sum
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.sum_cons, mkCall_f, mkCalls_sumB fs Bk σ xs]

/-- The body's frames under any `σ` total `osKidsB`. -/
theorem osBodyCalls_sumB (fs Bk : String → ℕ) (σ : Val) (c : OsCfg) :
    ((osBodyCalls σ c).map fun c' ↦ osCallB fs Bk c'.f).sum = osKidsB fs Bk c := by
  rw [osBodyCalls_eq, osKidsB]
  generalize (osBodyA c).filterMap Main.Stmt.callS = xs
  exact mkCalls_sumB fs Bk σ xs

/-- `CompleteAtB` on fewer words read. -/
theorem completeAtB_lin_mono {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {f : String}
    {Lin Lin' : Main.Layout} {args : List E} {Out : List E → Main.Layout → Prop} {B : ℕ}
    (h : CompleteAtB fs cert κ f Lin args Out B) (hsub : ∀ q ∈ Lin, q ∈ Lin') :
    CompleteAtB fs cert κ f Lin' args Out B := fun fp ↦ by
  obtain ⟨n, Lown, rets, Lout, ho, hw, hd, hn, hr⟩ := h fp
  refine ⟨n, Lown, rets, Lout, ho, hw, hd, hn, fun rd hl hm ↦ ?_⟩
  obtain ⟨h1, h2⟩ := Main.memL_append.mp hm
  have h3 : Main.MemL rd Lin := fun q hq ↦ h2 q (hsub q hq)
  exact (hr rd hl (Main.memL_append.mpr ⟨h1, h3⟩)).mono fun i ⟨q, hq, hq1, hq2⟩ ↦
    ⟨q, hsub q hq, hq1, hq2⟩

end
end LeanVM.Guest.B1
