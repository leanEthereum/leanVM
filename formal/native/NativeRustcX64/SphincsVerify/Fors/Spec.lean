module

public import NativeRustcX64.SphincsVerify.Fors.Leaf
public import NativeRustcX64.SphincsVerify.Fors.TreeEnd

/-!
# Region 3 on x86-64, the FORS trees (`b58 .. b96`): `ForsSpec`

From `AtFors` the first tree's head (`atTree_zero`); a tree (`tree_spec`): its head and leaf
(`tree_head`), its ten nodes (`nodes_spec`: `node_head`, `node_mid`, `node_tail`), its root
stored (`tree_end`); the 24 trees by induction (`trees_spec`): `AtForsKey` at `b97`
(**`fors_spec`**).
-/

namespace NativeRustcX64.SphincsVerifyProof.Fors

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym

public section

variable [Host] {r : Run}

omit [Host] in
/-- **The first tree's head** is `AtFors`. -/
theorem atTree_zero [Labels] {m : MachineData} (h : r.AtFors m) : AtTree r 0 m := by
  obtain ⟨hF, hI, h13, h15, hbp, h12, h14, h80, h60, hl, h568, h176, hbx⟩ := h
  exact ⟨⟨hF, by decide, hI, h176, h568, h80, h60, hl, fun i hi ↦ absurd hi (by simp [rootsUpTo])⟩,
    h13, h12, h14, h15, hbp, hbx⟩

/-- A state at a known pc, then on. -/
theorem ev_at {R : MachineState → Prop} {st : MachineState} {a : Int64} (h : st.pc = a)
    (k : Eventually (step1 Host.exe) R ⟨st.data, a⟩) : Eventually (step1 Host.exe) R st :=
  Chains.pc_at h k

/-- **A tree's nodes** from height `z`: its root at `b96`. -/
theorem nodes_spec (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {c : Nat} : ∀ n z, z + n = 10 → ∀ m, AtNode r c z m →
      Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b96Offset ∧ AtRoot r c st.data)
        ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b65Offset⟩ := by
  intro n
  induction n with
  | zero => intro z hn m h; exact absurd h.hz (by omega)
  | succ n ih =>
    intro z hn m h
    exact node_head hp hc hpre h fun m₁ h₁ ↦ node_mid hp hc hpre h₁ fun m₂ h₂ ↦
      node_tail hp hc hpre h₂ (fun _ m₃ h₃ ↦ ih (z + 1) (by omega) m₃ h₃)
        (fun _ m₃ h₃ ↦ .done _ ⟨rfl, h₃⟩)

/-- **A tree**: from its head, the next tree's head, or after the 24th, `b97`. -/
theorem tree_spec (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {c : Nat} {m : MachineData} (h : AtTree r c m) :
    Eventually (step1 Host.exe)
      (fun st ↦ (c + 1 < 24 ∧ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b58Offset ∧ AtTree r (c + 1) st.data) ∨
        (c + 1 = 24 ∧ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b97Offset ∧ r.AtForsKey st.data)) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b58Offset⟩ :=
  tree_head hp hc hpre h fun m₁ h₁ ↦
    Eventually.bind (nodes_spec hp hc hpre 10 0 rfl m₁ h₁) fun _ ⟨hpc, h₂⟩ ↦
      ev_at hpc (tree_end hp hpre h₂)

/-- **The trees** from tree `c`'s head. -/
theorem trees_spec (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre) :
    ∀ n c, c + n = 24 → ∀ m, AtTree r c m →
      Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b97Offset ∧ r.AtForsKey st.data)
        ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b58Offset⟩ := by
  intro n
  induction n with
  | zero => intro c hn m h; exact absurd h.keep.2.hc (by omega)
  | succ n ih =>
    intro c hn m h
    refine Eventually.bind (tree_spec hp hc hpre h) fun st hst ↦ ?_
    rcases hst with ⟨-, hpc, h'⟩ | ⟨-, hpc, h'⟩
    · exact ev_at hpc (ih (c + 1) (by omega) _ h')
    · exact .done _ ⟨hpc, h'⟩

end

end NativeRustcX64.SphincsVerifyProof.Fors

namespace NativeRustcX64.SphincsVerifyProof

/-- **Region 3, the FORS trees**: from `AtFors` at `b58`, `AtForsKey` at `b97`. -/
public theorem fors_spec [Host] : ForsSpec := fun _ hp hc hpre m h ↦
  Fors.trees_spec hp hc hpre 24 0 rfl m (Fors.atTree_zero h)

/--
info: 'NativeRustcX64.SphincsVerifyProof.fors_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fors_spec

end NativeRustcX64.SphincsVerifyProof
