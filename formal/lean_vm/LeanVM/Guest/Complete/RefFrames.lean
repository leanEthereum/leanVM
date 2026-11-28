/-
  LeanVM.Guest.Complete.RefFrames

  The reference run's frames: every state's frame a power below `2^κ`, each `KECCAK`'s a multiple of
  the window, from the tree track along the run.
-/

module

public import LeanVM.Guest.EndExecX
public import LeanVM.Guest.ExecWindows

/-!
# The reference run's frames

`Ref.Ok`'s `frames` and `aligned` (`FramesIn`, `KeccakFramesAligned`) on a reference run of the
honest tree that is a valid execution (`refFrames_of`). Past the prologue every state of the run is a
state of the tree track (`traceRef`), whose top frame is an honest instance, so a power below `2^κ`
(`honestA_within`); in the prologue and at the end the frame is `0`. At a `KECCAK` the track's top
function holds a `KECCAK` in its code (`ProgAl.fetch`), so it is allocated aligned (`KecAl`), and an
aligned instance's frame is a multiple of the window (`instsA_al`): a fresh callee's at
`allocBase true` (`allocBase_aligned`), a loop's tail call's right after its caller's, the same
function (`LastSelf`), whose aligned frame size is a multiple of the window (`LoopFsAl`).

`traceRef` reads what each frame's jumps read (`JumpCells`). `JumpCellsAt` asks it under `r.Ok`,
which holds the frames themselves; `JumpCellsV` asks it under `RefH` and `ValidExecution` only, the
premises of `RefFrames`, and gives `JumpCellsAt` (`JumpCellsV.toAt`).

The deployed instance's facts are `RefFramesCore.lean`'s.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core
open LeanVM.Prover.Exec (allocBase keccakWindow)

@[expose] public section

/-- **A loop helper's last call is to itself**, on every path that returns. -/
def LastSelf (P : Core.Program) : Prop :=
  ∀ f fn σ es vs, P.find? f = some fn → fn.loop = true → walk σ fn.body = .ret es vs →
    ∀ c, (calls es).getLast? = some c → c.f = f

/-- **An aligned loop helper's frame is a multiple of the window**, so its iterations' frames are
aligned together. -/
def LoopFsAl (P : Core.Program) (fs : String → ℕ) (al : String → Bool) : Prop :=
  ∀ f, P.loop f = true → al f = true → fs f % 16 = 0

section Aligned

variable {P : Core.Program} {rd : Reader} {fs : String → ℕ} {lp al : String → Bool}
  {H : Inst → ℕ → E × E}

/-- The callees' names are the calls'. -/
theorem kidsValid_names {σ : Val} : ∀ {cs : List Call} {ks : List Tree}, Tree.KidsValid P rd σ cs ks →
    ks.map Tree.name = cs.map Call.f
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨hn, _, h⟩ => by rw [List.map_cons, List.map_cons, hn, kidsValid_names h]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- Fresh callees: an aligned one's frame at a multiple of the window. -/
theorem posF_al : ∀ (c : ℕ) (ks : List Tree), ∀ q ∈ ks.zip (posF fs lp al c ks), al q.1.name = true →
    q.2.1 % 16 = 0
  | _, [], q, h, _ => by simp [posF] at h
  | c, k :: ks, q, h, ha => by
      simp only [posF, List.zip_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · show allocBase (al k.name) c % 16 = 0
        rw [show al k.name = true from ha]
        exact allocBase_aligned c
      · exact posF_al _ ks q h ha

/-- **A node's callees**: an aligned one's frame at a multiple of the window, given its own when
it is aligned. -/
theorem kidPosA_al (hlast : LastSelf P) (hfs : LoopFsAl P fs al) {p : ℕ × ℕ} {f : String} {σ : Val}
    {bufs : List ℕ} {kids : List Tree} {fn : Fn} {es : List Ev} {vs : List V} (hf : P.find? f = some fn)
    (hw : walk σ fn.body = .ret es vs) (hk : Tree.KidsValid P rd σ (calls es) kids)
    (hp : al f = true → p.1 % 16 = 0) :
    ∀ q ∈ kids.zip (kidPosA fs P.loop al p f bufs kids), al q.1.name = true → q.2.1 % 16 = 0 := by
  unfold kidPosA
  split
  · rename_i hl
    rcases List.eq_nil_or_concat kids with rfl | ⟨l, b, rfl⟩
    · intro q hq; simp at hq
    rw [List.concat_eq_append] at hk ⊢
    rw [(posL_split (fs := fs) (lp := P.loop) (al := al) (tl := p.1 + fs f)
      (c := p.2 + bufs.sum) (l := l) (b := b)).1,
      List.zip_append (by rw [length_posF])]
    intro q hq ha
    rcases List.mem_append.mp hq with hq | hq
    · exact posF_al _ _ q hq ha
    · simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hq
      subst hq
      have hnames := kidsValid_names hk
      have hlast' : ((calls es).map Call.f).getLast? = some b.name := by
        rw [← hnames, List.map_append, List.map_cons, List.map_nil, List.getLast?_append]
        simp
      rw [List.getLast?_map] at hlast'
      obtain ⟨c, hc, hcf⟩ := Option.map_eq_some_iff.mp hlast'
      have hloop : fn.loop = true := by rw [← Program.loop_of_find? hf]; exact hl
      have hbf : b.name = f := hcf ▸ hlast f fn σ es vs hf hloop hw c hc
      simp only at ha ⊢
      rw [hbf] at ha
      have h1 := hp ha
      have h2 := hfs f hl ha
      omega
  · exact posF_al _ _

mutual
/-- **An aligned instance's frame is a multiple of the window**, in a valid tree placed at a
position aligned when its root is. -/
theorem instsA_al (hlast : LastSelf P) (hfs : LoopFsAl P fs al) :
    ∀ (t : Tree) (p : ℕ × ℕ) (hdr : E × E) {args rets : List E}, t.Valid P rd args rets →
      (al t.name = true → p.1 % 16 = 0) →
      ∀ I ∈ t.instsA fs P.loop al H p hdr, al I.t.name = true → I.fp % 16 = 0
  | .node f σ bufs kids, p, hdr, args, rets, hv, hp, I, hI, ha => by
      rw [instsA_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · exact hp ha
      · obtain ⟨fn, hf, -, es, vs, hw, -, -, hk⟩ := hv
        exact instsKidsA_al hlast hfs kids σ (calls es) _ 0 _ hk
          (kidPosA_al hlast hfs hf hw hk hp) I hI ha
  | .phantom .., _, _, _, _, hv, _, _, _, _ => hv.elim

/-- `instsA_al` for the callees at `ps`. -/
theorem instsKidsA_al (hlast : LastSelf P) (hfs : LoopFsAl P fs al) :
    ∀ (ks : List Tree) (σ : Val) (cs : List Call) (I : Inst) (j : ℕ) (ps : List (ℕ × ℕ)),
      Tree.KidsValid P rd σ cs ks → (∀ q ∈ ks.zip ps, al q.1.name = true → q.2.1 % 16 = 0) →
      ∀ J ∈ Tree.instsKidsA fs P.loop al H I j ps ks, al J.t.name = true → J.fp % 16 = 0
  | [], _, _, _, _, _, _, _, J, hJ, _ => by rw [instsKidsA_nil] at hJ; exact (List.not_mem_nil hJ).elim
  | _ :: _, _, _, _, _, [], _, _, J, hJ, _ => by
      rw [instsKidsA_nil_left] at hJ; exact (List.not_mem_nil hJ).elim
  | k :: ks, σ, c :: cs, I, j, p :: ps, ⟨_, hc, hks⟩, hq, J, hJ, ha => by
      rw [instsKidsA_cons, List.mem_append] at hJ
      have hq0 : al k.name = true → p.1 % 16 = 0 := hq (k, p) (by simp)
      have hqs : ∀ q ∈ ks.zip ps, al q.1.name = true → q.2.1 % 16 = 0 :=
        fun q h ↦ hq q (by simp [h])
      rcases hJ with hJ | hJ
      · by_cases ht : c.taken = true
        · rw [ite_eq_left ht] at hc
          exact instsA_al hlast hfs k _ _ hc hq0 J hJ ha
        · rw [ite_eq_right ht] at hc
          obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
          rw [instsA_phantom, List.mem_singleton] at hJ
          subst hJ
          exact hq0 ha
      · exact instsKidsA_al hlast hfs ks σ cs I (j + 1) ps hks hqs J hJ ha
  | _ :: _, _, [], _, _, _ :: _, h, _, _, _, _ => h.elim
end

end Aligned

end

end LeanVM.Guest.Memory

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge hiding St
open LeanVM.Prover.Exec

@[expose] public section

/-- **What each frame's jumps read**, on every reference run of the honest tree that is a valid
execution: `JumpCellsAt` without the frames `r.Ok` holds. -/
def JumpCellsV (L : Lay) (D : Ref → RefD) (A : String → FnAl) : Prop :=
  ∀ r, RefH L (D r) r → ValidExecution guestProgram r.input r.exec → ∀ pc fp done e st,
    RefTrack L D A r pc fp (done, e :: st) → JumpCells r.img A e pc

/-- **A function whose code holds a `KECCAK` is allocated aligned.** -/
def KecAl (al : String → Bool) (A : String → FnAl) : Prop :=
  ∀ f fn, coreProgram.find? f = some fn → ∀ (off : ℕ) (ins : OffsetInstruction), (A f).code[off]? = some ins →
    ins.toLeanIsaInstruction.opcode = Opcode.keccak → al f = true

variable {L : Lay} {D : Ref → RefD} {A : String → FnAl}

theorem JumpCellsV.toAt (h : JumpCellsV L D A) : JumpCellsAt L D A :=
  fun r hR hr ↦ h r hR hr.valid

/-- An honest instance's frame is below `2^κ`. -/
theorem inst_fp_lt_pow {r : Ref} (hR : RefH L (D r) r) {I : Inst} (hI : I ∈ instsOf L (D r) r) :
    I.fp < 2 ^ r.κ := by
  obtain ⟨rd, hH, -⟩ := hR.honest
  have h2 := hH.cells.two_le I hI
  have hw := honestA_within hI (by omega)
  have hle := le_two_pow_logMem ((D r).T.wordsA L.fs coreProgram.loop L.al)
  rw [hR.κ]
  omega

/-- **An aligned honest instance's frame is a multiple of the window.** -/
theorem inst_aligned (hlast : LastSelf coreProgram) (hfs : LoopFsAl coreProgram L.fs L.al) {r : Ref}
    (hR : RefH L (D r) r) {I : Inst} (hI : I ∈ instsOf L (D r) r) (ha : L.al I.t.name = true) :
    I.fp % 16 = 0 := by
  obtain ⟨rd, hH, -⟩ := hR.honest
  exact instsA_al hlast hfs (D r).T _ _ hH.valid (fun _ ↦ Nat.zero_mod 16) I hI ha

/-- **Past the prologue, a state of the run is one of the tree track's**, at its registers. -/
theorem track_of_run (hP : ProgAl guestProgram coreProgram A) (hmain : entOf A "main" = proLen)
    (hJ : JumpCellsV L D A) {r : Ref} (hR : RefH L (D r) r)
    (hv : ValidExecution guestProgram r.input r.exec) {k : ℕ} (hk1 : proLen ≤ k) (hk2 : k < r.n)
    {rg : Registers K} (hrg : run guestProgram r.img k Registers.initial = some rg) :
    ∃ pc fp done e st, rg = regs pc fp ∧ RefTrack L D A r pc fp (done, e :: st) := by
  have hrun : run guestProgram r.img r.n Registers.initial = some (Registers.final guestProgram) := hv.2
  have hN : run guestProgram r.img (r.n - proLen) (regs proLen 0) = some (Registers.final guestProgram) := by
    have h := run_add guestProgram r.img proLen (r.n - proLen) Registers.initial
    rw [show proLen + (r.n - proLen) = r.n by omega, hrun, hR.pro proLen le_rfl, Option.bind_some] at h
    exact h.symm
  obtain ⟨tr, htr⟩ := traceRef hP hmain hR (hJ r hR hv) hN
  obtain ⟨h1, h2⟩ := htr (k - proLen) (by omega)
  have hk : run guestProgram r.img k Registers.initial = run guestProgram r.img (k - proLen) (regs proLen 0) := by
    have h := run_add guestProgram r.img proLen (k - proLen) Registers.initial
    rw [show proLen + (k - proLen) = k by omega, hR.pro proLen le_rfl, Option.bind_some] at h
    exact h
  rw [hk, h1] at hrg
  obtain ⟨e, st', hst, -⟩ := h2.top
  refine ⟨_, _, (tr (k - proLen)).2.2.1, e, st', (Option.some.inj hrg).symm, ?_⟩
  rw [← hst]
  exact h2

/-- **The reference run's frames**: on a reference run of the honest tree that is a valid
execution, every state's frame is a power below `2^κ` and each `KECCAK`'s a multiple of the
window. -/
theorem refFrames_of (hP : ProgAl guestProgram coreProgram A) (hmain : entOf A "main" = proLen)
    (hJ : JumpCellsV L D A) (hK : KecAl L.al A) (hlast : LastSelf coreProgram)
    (hfs : LoopFsAl coreProgram L.fs L.al) :
    ∀ r, RefH L (D r) r → ValidExecution guestProgram r.input r.exec →
      FramesIn guestProgram r.img r.n ∧ Mode.KeccakFramesAligned guestProgram r.img r.n := by
  intro r hR hv
  have hrun : run guestProgram r.img r.n Registers.initial = some (Registers.final guestProgram) := hv.2
  have h0 : (0 : ℕ) < 2 ^ r.κ := Nat.two_pow_pos _
  refine ⟨fun k hk rg hrg ↦ ?_, fun k hk rg hrg ins hf hop ↦ ?_⟩
  · rcases Nat.lt_or_ge proLen k with hkp | hkp
    swap
    · rw [hR.pro k hkp, Option.some.injEq] at hrg
      subst hrg
      exact ⟨0, h0, by rw [regs_eq]⟩
    rcases lt_or_eq_of_le hk with hlt | rfl
    · obtain ⟨pc, fp, done, e, st, rfl, htr⟩ := track_of_run hP hmain hJ hR hv hkp.le hlt hrg
      obtain ⟨e', st', he, hE, hfp, -⟩ := htr.top
      obtain rfl : e = e' := (List.cons.inj he).1
      exact ⟨fp, hfp ▸ inst_fp_lt_pow hR hE.mem, by rw [regs_eq]⟩
    · rw [hrun, Option.some.injEq] at hrg
      subst hrg
      exact ⟨0, h0, by simp [Registers.final, fpFinal]⟩
  · rcases Nat.lt_or_ge proLen k with hkp | hkp
    swap
    · rw [hR.pro k hkp, Option.some.injEq] at hrg
      subst hrg
      exact ⟨0, h0, by rw [regs_eq], by simp [keccakWindow]⟩
    obtain ⟨pc, fp, done, e, st, rfl, htr⟩ := track_of_run hP hmain hJ hR hv hkp.le hk hrg
    obtain ⟨e', st', he, hE, hfp, off, hpc, p, hal, -⟩ := htr.top
    obtain rfl : e = e' := (List.cons.inj he).1
    obtain ⟨ins0, -, -, -, -, hins, -⟩ := alignAt_step (hP.ok _ _ hE.find) hal
    have hfetch := hP.fetch _ _ hE.find off ins0 hins
    rw [regs_eq] at hf
    have hpc' : (A e.I.t.name).X.entry + off = pc := hpc.symm
    rw [hpc'] at hfetch
    rw [show (g ^ pc : K) = addressOfIndex pc from rfl, hfetch, Option.some.injEq] at hf
    subst hf
    have hal' := hK _ _ hE.find off ins0 hins hop
    refine ⟨fp, hfp ▸ inst_fp_lt_pow hR hE.mem, by rw [regs_eq], ?_⟩
    rw [← hfp]
    exact inst_aligned hlast hfs hR hE.mem hal'

end

end LeanVM.Guest.EndExec
