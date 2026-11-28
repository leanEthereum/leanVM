/-
  LeanVM.Guest.CoreMode.Fn.squeeze_packed.SoundA

  `squeeze_packed`'s own family, sound at the honest instances of b2c's aligned tree (`OwnOkA`): its count `g^p`,
  `p < 64`, from its meaning (`B1.Link.squeeze_packed_sound`).
-/

module

public import LeanVM.Guest.EndExecCoreResA
public import LeanVM.Guest.CoreMode.Fn.squeeze_packed.Fam
public import LeanVM.Guest.B1.Link.SqueezePacked
import LeanVM.Guest.CoreRef
import LeanVM.Guest.CoreMode.Fam.MonoChain
import LeanVM.Guest.CoreMode.Fam.ProgOkG
import LeanVM.Guest.EndExecInstA

namespace LeanVM.Guest.CoreMode.Own.squeeze_packed

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec

public section

theorem find_sp : coreProgram.find? name% «squeeze_packed» = some fn% «squeeze_packed» :=
  coreProgram_find?_at (j := idx% «squeeze_packed») rfl

/-- **Its count** at an honest instance: `count_g = g^p`, `p < 64`. -/
theorem sp_count {al : String → Bool} {D : Ref → RefD} {r : Ref} (hR : RefH (layB al) (D r) r) {I : Inst}
    (hI : I ∈ instsR al D r) {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (ht : I.t = .node name% «squeeze_packed» σ bufs kids) :
    ∃ p < 64, σ (.n 6) = LeanVM.Protocol.Verifier.gen ^ p := by
  obtain ⟨args, rets, hv⟩ := inst_validA hR hI ht
  obtain ⟨hp, -⟩ := Res.holds_of_valid Res.fs_pos hv find_sp
  have M := B1.Link.squeeze_packed_sound _ _ _ (Memory.Tree.Valid.rel _ hv)
  have hargs : args = [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6)] := by
    rw [← hp]; rfl
  subst hargs
  simp only [B1.Link.MeaningSP] at M
  obtain ⟨p, hp64, hcg, -⟩ := M
  exact ⟨p, hp64, hcg⟩

/-- **Its family** (`countFam`), aligned. -/
theorem fams_okA {al : String → Bool} {D : Ref → RefD} : ∀ c ∈ fams, OwnOkA al D c := by
  intro c hc r hR hr I hI σ bufs kids ht fn hf x hx
  simp only [fams, List.mem_singleton] at hc
  subst hc
  simp only at hx ht
  obtain ⟨p, hp64, hcg⟩ := sp_count hR hI ht
  unfold countFam at hx
  split at hx
  · rename_i y m
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.blt_eq] at hx
    obtain ⟨⟨rfl, h64⟩, hm⟩ := hx
    exact ltF_of_pow hm (by omega) (hcg.trans (Value.gen_pow_eq_ofK _))
  · cases hx

end

end LeanVM.Guest.CoreMode.Own.squeeze_packed
