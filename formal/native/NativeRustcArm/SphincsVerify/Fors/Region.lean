module

public import NativeRustcArm.SphincsVerify.Fors.TreeC

/-!
# Region 3, the FORS trees (`b59 .. b93`): `ForsSpec`

`b59` sets the trees' loop up from `AtFors` (`fors_entry`); a tree (`tree_spec`): its head and
leaf (`tree_s1`, `tree_s2`), its ten nodes (`nodes_spec`), its root stored (`tree_end`); the 24
trees by induction (`trees_spec`): `AtForsKey` at `b94` (**`fors_spec`**).
-/

namespace NativeRustcArm.SphincsVerifyProof.Fors

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcArm.Sphincs.SphincsVerify

public section

variable {r : Run} [Host]

/-- **The loop's set-up** (`b59`): from `AtFors`, the first tree's head. -/
theorem fors_entry (hp : Placed code r.k) (hpre : r.Pre) {m : MachineData} (h : r.AtFors m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b60Offset ∧ AtTree r 0 st.data) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b59Offset⟩ := by
  obtain ⟨hF, hIn, h22, h20, h24, h21, h23, hleaves, h392⟩ := h
  have hwf := r.frame_wf hpre hF (fun _ ↦ 0)
  have hm : Match (r.env m) s59 m :=
    r.match_frame hpre hF ⟨hF.2.1.trans (eval_ptr 29280).symm, known_ptr h24, known_ptr h21,
      known_ptr h23, trivial⟩ trivial trivial trivial
  refine exec_then (hb59 hp) run_b59 hwf hm fun st1 hm1 hpc1 ↦ ?_
  have hF1 : r.Frame st1.data := Run.Frame.of_match r hpre hF hm1 hwf rfl rfl rfl
  have hkeep : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 29376 →
      Run.noWriteIn _ o bs.length = true → BytesAt m.dmem (r.off o) bs →
      BytesAt st1.data.dmem (r.off o) bs := fun ho hn h ↦ r.bytesAt_kept hpre hm1 hwf ho h hn
  have h22' : (m.regs.getXReg .X22).toBitVec = r.idx.toBitVec := h22
  have hB : Base r st1.data := by
    refine ⟨hF1, ⟨hkeep (by rw [length_pkBytes]; decide) (by rw [length_pkBytes]; rfl) hIn.1,
      hkeep (by rw [Run.length_sigMem]; decide) (by rw [Run.length_sigMem]; rfl) hIn.2.1,
      hkeep (by rw [length_wordBytes]; decide) (by rw [length_wordBytes]; rfl) hIn.2.2⟩,
      ?_, hkeep (by rw [length_wordBytes]; decide) (by rw [length_wordBytes]; rfl) h392, ?_, ?_,
      hkeep (by rw [length_leavesMem]; decide) (by rw [length_leavesMem]; rfl) hleaves,
      hm1.regs .X20 _ rfl, (hm1.regs .X21 _ rfl).trans (eval_ptr 16600),
      (hm1.regs .X22 _ rfl).trans (eval_ptr 26968)⟩
    · refine write_reg hm1 (o := 384) (n := 8) (x := .X22) (by decide) (by decide) ?_
      rw [bytes_reg, h22']
    · refine write_val hm1 (o := 400) (n := 8) rfl (by decide) (by decide) ?_
      rw [bytes_reg]
      exact congrArg wordBytes (congrArg UInt64.ofBitVec (eval_ptr 25752))
    · refine write_val hm1 (o := 408) (n := 8) rfl (by decide) (by decide) ?_
      rw [bytes_reg]
      simp only [Sym.eval, Env.ofMachine_regs]
      rw [h22']
      exact wordBytes_treeW r
  refine .done _ ⟨hpc1.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b59_next), ⟨⟨hB, by decide, fun i hi ↦ by simp at hi⟩,
    hm1.regs .X19 _ rfl, ?_, (hm1.regs .X9 _ rfl).trans (eval_ptr 8244), hm1.regs .X8 _ rfl, ?_,
    hm1.regs .X25 _ rfl, ?_, ?_⟩⟩
  · exact (hm1.regs .X24 _ rfl).trans (eval_ptr 25752)
  · exact (hm1.regs .X23 _ rfl).trans (eval_ptr 21648)
  · rw [Run.RegIs, hm1.regs .X26 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [show (m.regs.getXReg .X20).toBitVec = (r.idx &&& 255).toBitVec from h20]
    rfl
  · rw [show st1.data.regs.getXReg .X27 = UInt64.ofBitVec (treeW r) from
      UInt64.toBitVec_inj.mp ((hm1.regs .X27 _ rfl).trans (by
        simp only [Sym.eval, Env.ofMachine_regs]; rw [h22']; rfl))]
    exact wordBytes_treeW r

/-- **A tree** (`b60 .. b93`): from its head, the next tree's head, or after the 24th, `b94`. -/
theorem tree_spec (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {c : Nat} {m : MachineData}
    (h : AtTree r c m) :
    Eventually (step1 Host.exe)
      (fun st ↦ (c + 1 < 24 ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b60Offset ∧ AtTree r (c + 1) st.data) ∨
        (c + 1 = 24 ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b94Offset ∧ r.AtForsKey st.data)) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b60Offset⟩ := by
  refine Eventually.bind (tree_s1 hp hc hpre h) fun st ⟨hpc, h1⟩ ↦ ev_at hpc ?_
  refine Eventually.bind (tree_s2 hp hc hpre h1) fun st ⟨hpc, h2⟩ ↦ ev_at hpc ?_
  refine Eventually.bind (nodes_spec hp hc hpre 10 0 rfl _ h2) fun st ⟨hpc, h3⟩ ↦ ev_at hpc ?_
  exact tree_end hp hpre h3

/-- **The trees** from tree `c`'s head. -/
theorem trees_spec (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) :
    ∀ n c, c + n = 24 → ∀ m, AtTree r c m →
      Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b94Offset ∧ r.AtForsKey st.data)
        ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b60Offset⟩ := by
  intro n
  induction n with
  | zero => intro c hn m h; exact absurd h.rs.hc (by omega)
  | succ n ih =>
    intro c hn m h
    refine Eventually.bind (tree_spec hp hc hpre h) fun st hst ↦ ?_
    rcases hst with ⟨-, hpc, h'⟩ | ⟨-, hpc, h'⟩
    · exact ev_at hpc (ih (c + 1) (by omega) _ h')
    · exact .done _ ⟨hpc, h'⟩

end

end NativeRustcArm.SphincsVerifyProof.Fors

namespace NativeRustcArm.SphincsVerifyProof

/-- **Region 3, the FORS trees**: from `AtFors` at `b59`, `AtForsKey` at `b94`. -/
public theorem fors_spec [NativeRustcArm.Host] : ForsSpec := by
  intro r hp hc hpre m h
  refine Eventually.bind (Fors.fors_entry hp hpre h) fun st ⟨hpc, h0⟩ ↦ Fors.ev_at hpc ?_
  exact Fors.trees_spec hp hc hpre 24 0 rfl _ h0

end NativeRustcArm.SphincsVerifyProof
