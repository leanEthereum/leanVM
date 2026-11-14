/-
  LeanVM.Guest.B1.Sig.Interface

  The interface of B1's signature verifiers at the guest's `coreProgram`: `InterfaceP.lean`'s
  statements instantiated, the functions found, and the call relation's consequences.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Main.Frames
public import LeanVM.Guest.B1.Sig.InterfaceP
public import LeanVM.Guest.B1.Common.Find

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **`verify_sig_lean_sphincs` is sound** in the guest's `coreProgram` (`InterfaceP.lean`). -/
def verify_sig_lean_sphincs_sound_Spec (sigOf : Val → FrameMap → Sphincs.Signature) : Prop :=
  verify_sig_lean_sphincs_sound_SpecP coreProgram sigOf

/-! ## The functions, found -/

theorem verify_sig_lean_sphincs_params : (fn% «verify_sig_lean_sphincs»).params = [.n 0, .n 1] :=
  rfl

theorem find_sp_wots : coreProgram.find? "sp_wots" = some fn% «sp_wots» :=
  coreProgram_find?_at (j := idx% «sp_wots») rfl

instance finds_sp_wots : Finds coreProgram "sp_wots" Fn.«sp_wots».core := ⟨find_sp_wots⟩

theorem find_verify_sig_lean_sphincs :
    coreProgram.find? "verify_sig_lean_sphincs" = some fn% «verify_sig_lean_sphincs» :=
  coreProgram_find?_at (j := idx% «verify_sig_lean_sphincs») rfl

/-! ## The call relation, from the statements -/

variable {rd : Reader}

theorem rel_iff_body {name : String} {fn : Fn} (h : coreProgram.find? name = some fn)
    (args rets : List E) :
    coreProgram.Rel rd name args rets ↔
      ∃ σ : Val, fn.params.map σ = args ∧
        Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False (fun rs => rs = rets) := by
  rw [rel_iff]
  simp only [h, Option.some.injEq, exists_eq_left', Fn.Sem]

/-- **A call of `verify_sig_lean_sphincs`** on a memory image of at most `2^32` words takes two
arguments, returns nothing, and when the second holds the byte table the claim at the first is
signed. -/
theorem verify_sig_lean_sphincs_signed {sigOf : Val → FrameMap → Sphincs.Signature}
    (hs : verify_sig_lean_sphincs_sound_Spec sigOf) {κ : ℕ} {L : MemoryImage κ} (hκ : κ ≤ 32)
    {args rets : List E} (h : coreProgram.Rel L.read "verify_sig_lean_sphincs" args rets) :
    ∃ p bb, args = [p, bb] ∧ rets = [] ∧ (ByteBits L.read bb → SphincsSigned L.read p) := by
  obtain ⟨σ, hp, hb⟩ := (rel_iff_body find_verify_sig_lean_sphincs args rets).mp h
  obtain ⟨hr, ho⟩ := hs _ (relV L.read) L hκ (unfoldsV_rel L.read) σ rets hb
  exact ⟨σ (.n 0), σ (.n 1), by rw [← hp]; rfl, hr, fun hbb => ⟨_, ho hbb⟩⟩

end
end LeanVM.Guest.B1.Sig
