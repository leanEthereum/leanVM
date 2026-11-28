/-
  LeanVM.Guest.B2C.ShareChecked

  A compiled function passes the local sharing check on its own data.
-/

module

public import LeanVM.Guest.B2C.ShareL
public import LeanVM.Guest.B2C.Defs
public import LeanVM.Guest.CheckWinC

/-!
# The sharing check held

`ShareChecked j`: function `j`'s core IR and certificate (a `Check.Link`), its completeness data
and frame size pass `ShareL.shareCheckL` with some certificate of the check. The generated glue
(`B2C/Shared/Fn*`) proves it from the packs' kernel checks (`shareChecked_of_link`) and imports
only the check's definitions, which `CertFirewall` guards; `B2C.ShareLink` turns it into what the
proofs read, `ShareOk j`.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Guest LeanVM.Guest.Check

@[expose] public section

/-- **Function `j` passes the sharing check**: over a link's core IR `cf` and certificate `C`,
`main` saying whether `j` is `main`, `mc` its bound on the cells. -/
def ShareChecked (j : ℕ) : Prop :=
  ∃ (G : Glob) (f : CompiledFunction) (cf : Core.Fn) (C : Cert) (main : Bool) (mc : ℕ) (T : ShareL.Tabs),
    Link j G f cf C ∧ Nat.beq j 1 = main ∧ (main = true → Data.mainCells = mc) ∧
      ShareL.shareCheckL cf C (plumbOf j) (fsN j) main mc T = true

theorem shareChecked_of_link {j : ℕ} {G : Glob} {f : CompiledFunction} {cf : Core.Fn} {C : Cert} {P : Plumb}
    {fs : ℕ} {main : Bool} {mc : ℕ} {T : ShareL.Tabs} (h : Link j G f cf C) (hP : plumbOf j = P)
    (hfs : fsN j = fs) (hm : Nat.beq j 1 = main) (hmc : main = true → Data.mainCells = mc)
    (ok : ShareL.shareCheckL cf C P fs main mc T = true) : ShareChecked j :=
  ⟨G, f, cf, C, main, mc, T, h, hm, hmc, hP ▸ hfs ▸ ok⟩

end
end LeanVM.Guest.B2C
