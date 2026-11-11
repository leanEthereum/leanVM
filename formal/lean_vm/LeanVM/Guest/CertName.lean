/-
  LeanVM.Guest.CertName

  The certificate of a guest function by its name.
-/

module

public import LeanVM.Guest.Glob
public import LeanVM.Guest.NameIndex
public import LeanVM.Guest.CheckSound

/-!
# Certificates by name

The located call relation (`Check.RL`) reads a callee's values off its frame through the callee's
certificate, which it finds by the callee's name: `certByName f` is the certificate of the first
function of `coreProgram` named `f` (`certOf (nameIndex f)`, `NameIndex.lean`), and, the names
being distinct (`coreProgram_names_nodup`), `certByName (coreOf j).name = certOf j`
(`certByName_coreOf`).
-/

namespace LeanVM.Guest

open LeanVM.Guest.Check

@[expose] public section

/-- The certificate of the function named `f`: `certOf` at its index (`nameIndex`: one past its
position in `coreProgram`, `main` is function `1`). -/
noncomputable def certByName (f : String) : Cert := certOf (nameIndex f)

theorem certByName_coreOf {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) :
    certByName (coreOf j).name = certOf j := by
  have hl : j - 1 < coreProgram.length := by
    have : coreProgram.length = 1752 := coreProgram_length
    simp only [nFns] at h2
    omega
  unfold certByName nameIndex coreOf
  rw [nth_eq hl, findIdx_name_of_nodup coreProgram_names_nodup hl]
  congr 1
  omega

end
end LeanVM.Guest
