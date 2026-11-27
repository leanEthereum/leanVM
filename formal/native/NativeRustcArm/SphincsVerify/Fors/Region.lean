module

public import NativeRustcArm.SphincsVerify.Fors.TreeC

/-!
# Region 3, the FORS trees (`b50 .. b84`): `ForsSpec`

`b50` sets the trees' loop up from `AtFors` (`fors_entry`); a tree (`tree_spec`): its head and
leaf (`tree_s1`, `tree_s2`), its ten nodes (`nodes_spec`), its root stored (`tree_end`); the 24
trees by induction (`trees_spec`): `AtForsKey` at `b85` (**`fors_spec`**).
-/

namespace NativeRustcArm.SphincsVerifyProof.Fors

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcArm.Sphincs.SphincsVerify

public section

variable {r : Run} [ElfHost]

/-- **The loop's set-up** (`b50`): from `AtFors`, the first tree's head. -/
theorem fors_entry (hp : PlacedIn code r.sec r.k) (hpre : r.Pre) {m : MachineData} (h : r.AtFors m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b51Offset ∧ AtTree r 0 st.data) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b50Offset⟩ := by
  obtain ⟨hF, hIn, h21, h19, h24, h20, h23, hleaves, h408⟩ := h
  have hwf := r.frame_wf hpre hF (fun _ ↦ 0)
  have hm : Match (r.env m) s50 m :=
    r.match_frame hpre hF ⟨hF.2.1.trans (eval_ptr 21520).symm, known_ptr h24, known_ptr h20,
      known_ptr h23, trivial⟩ trivial trivial trivial
  refine exec_then_elf (hb50 hp) run_b50 hwf hm fun st1 hm1 hpc1 ↦ ?_
  have hF1 : r.Frame st1.data := Run.Frame.of_match r hpre hF hm1 hwf rfl rfl rfl
  have hkeep : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 21616 →
      Run.noWriteIn _ o bs.length = true → BytesAt m.dmem (r.off o) bs →
      BytesAt st1.data.dmem (r.off o) bs := fun ho hn h ↦ r.bytesAt_kept hpre hm1 hwf ho h hn
  have h21' : (m.regs.getXReg .X21).toBitVec = r.idx.toBitVec := h21
  have hB : Base r st1.data := by
    refine ⟨hF1, ⟨hkeep (by rw [r.hpk]; decide) (by rw [r.hpk]; rfl) hIn.1,
      hkeep (by rw [Run.length_sigMem]; decide) (by rw [Run.length_sigMem]; rfl) hIn.2.1,
      hkeep (by rw [length_wordBytes]; decide) (by rw [length_wordBytes]; rfl) hIn.2.2⟩,
      ?_, hkeep (by rw [length_wordBytes]; decide) (by rw [length_wordBytes]; rfl) h408, ?_, ?_,
      hkeep (by rw [length_leavesMem]; decide) (by rw [length_leavesMem]; rfl) hleaves,
      hm1.regs .X28 _ rfl, (hm1.regs .X26 _ rfl).trans (eval_ptr 8840),
      (hm1.regs .X22 _ rfl).trans (eval_ptr 19208)⟩
    · refine write_reg hm1 (o := 400) (n := 8) (x := .X21) (by decide) (by decide) ?_
      rw [bytes_reg, h21']
    · refine write_val hm1 (o := 416) (n := 8) rfl (by decide) (by decide) ?_
      rw [bytes_reg]
      exact congrArg wordBytes (congrArg UInt64.ofBitVec (eval_ptr 17992))
    · refine write_val hm1 (o := 424) (n := 8) rfl (by decide) (by decide) ?_
      rw [bytes_reg]
      simp only [Sym.eval, Env.ofMachine_regs]
      rw [h21']
      exact wordBytes_treeW r
  refine .done _ ⟨hpc1.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b50_next), ⟨⟨hB, by decide, fun i hi ↦ by simp at hi⟩,
    hm1.regs .X19 _ rfl, ?_, (hm1.regs .X9 _ rfl).trans (eval_ptr 484), hm1.regs .X8 _ rfl, ?_,
    hm1.regs .X10 _ rfl, ?_, ?_⟩⟩
  · exact (hm1.regs .X24 _ rfl).trans (eval_ptr 17992)
  · exact (hm1.regs .X23 _ rfl).trans (eval_ptr 15936)
  · rw [Run.RegIs, hm1.regs .X25 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [show (m.regs.getXReg .X19).toBitVec = (r.idx &&& 255).toBitVec from h19]
    rfl
  · rw [show st1.data.regs.getXReg .X20 = UInt64.ofBitVec (treeW r) from
      UInt64.toBitVec_inj.mp ((hm1.regs .X20 _ rfl).trans (by
        simp only [Sym.eval, Env.ofMachine_regs]; rw [h21']; rfl))]
    exact wordBytes_treeW r

/-- **A tree** (`b51 .. b84`): from its head, the next tree's head, or after the 24th, `b85`. -/
theorem tree_spec (hp : PlacedIn code r.sec r.k) (hc : Callees) (hpre : r.Pre) {c : Nat} {m : MachineData}
    (h : AtTree r c m) :
    Eventually (elfStep1 ElfHost.exe)
      (fun st ↦ (c + 1 < 24 ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b51Offset ∧ AtTree r (c + 1) st.data) ∨
        (c + 1 = 24 ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b85Offset ∧ r.AtForsKey st.data)) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b51Offset⟩ := by
  refine Eventually.bind_elf (tree_s1 hp hc hpre h) fun st ⟨hpc, h1⟩ ↦ ev_at hpc ?_
  refine Eventually.bind_elf (tree_s2 hp hc hpre h1) fun st ⟨hpc, h2⟩ ↦ ev_at hpc ?_
  refine Eventually.bind_elf (nodes_spec hp hc hpre 10 0 rfl _ h2) fun st ⟨hpc, h3⟩ ↦ ev_at hpc ?_
  exact tree_end hp hpre h3

/-- **The trees** from tree `c`'s head. -/
theorem trees_spec (hp : PlacedIn code r.sec r.k) (hc : Callees) (hpre : r.Pre) :
    ∀ n c, c + n = 24 → ∀ m, AtTree r c m →
      Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b85Offset ∧ r.AtForsKey st.data)
        ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b51Offset⟩ := by
  intro n
  induction n with
  | zero => intro c hn m h; exact absurd h.rs.hc (by omega)
  | succ n ih =>
    intro c hn m h
    refine Eventually.bind_elf (tree_spec hp hc hpre h) fun st hst ↦ ?_
    rcases hst with ⟨-, hpc, h'⟩ | ⟨-, hpc, h'⟩
    · exact ev_at hpc (ih (c + 1) (by omega) _ h')
    · exact .done _ ⟨hpc, h'⟩

end

end NativeRustcArm.SphincsVerifyProof.Fors

namespace NativeRustcArm.SphincsVerifyProof

/-- **Region 3, the FORS trees**: from `AtFors` at `b50`, `AtForsKey` at `b85`. -/
public theorem fors_spec [ElfHost] : ForsSpec := by
  intro r hp hc hpre m h
  refine Eventually.bind_elf (Fors.fors_entry hp hpre h) fun st ⟨hpc, h0⟩ ↦ Fors.ev_at hpc ?_
  exact Fors.trees_spec hp hc hpre 24 0 rfl _ h0

end NativeRustcArm.SphincsVerifyProof
