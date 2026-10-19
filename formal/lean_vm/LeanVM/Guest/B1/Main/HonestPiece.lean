/-
  LeanVM.Guest.B1.Main.HonestPiece

  From a uniform placed relation of `main` at `0` to an honest tree (`HonestAt`): the memory image
  of the layout, the discharge's memory-side fields, its addresses, and `honestAt_retemp`.
-/

module

public import LeanVM.Guest.B1.Main.HonestImage
public import LeanVM.Guest.Memory.GuestFresh

/-!
# The honest tree

`KFacts`: the certificate's facts the discharge takes of a tree (group K). `dischargeAddr`: every
equation of a tree valid on a memory image and placed at `0` names a word of it, its loads and
range checks by validity, its `frameAddr` runs by their certificate cells in their frames.
`honest_of_relAtIn`: if `main` holds by a tree placed at `0` of `N ≤ 2^32` words on every memory
holding a consistent layout `L` in `[2, N)` and the header, an honest tree of `N` words exists.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1 (LowDef)

@[expose] public section

variable {P : Core.Program} {fs : String → ℕ} {cert : String → V → ℕ} {H : Inst → ℕ → E × E}
  {C : Inst → List (ℕ × E)} {hdr : E × E}

variable (P fs cert H C hdr) in
/-- **The certificate's facts about a tree** (group K): `DischargeHyps`' fields on the cells. -/
structure KFacts (T : Tree) : Prop where
  cells : CellsOk fs C (honestInsts P fs H hdr T)
  cells' : ∀ ν, CellsOk fs C (honestInsts P fs H hdr (T.retemp P fs ν 0))
  cert_lt : ∀ f, ∀ t ∈ P.temps f, 2 ≤ cert f t ∧ cert f t < fs f
  cert_inj : ∀ f, ∀ t ∈ P.temps f, ∀ t' ∈ P.temps f, cert f t = cert f t' → t = t'
  run : ∀ I ∈ honestInsts P fs H hdr T, ∀ f σ bufs kids, I.t = .node f σ bufs kids →
    ∀ p r rs, Ev.atom (.frameAddr p (r :: rs)) ∈ I.t.events P →
      ∀ (k : ℕ) (hk : k < (r :: rs).length), (cert f r + k, σ (r :: rs)[k]) ∈ C I ∧
        ∀ t ∈ P.temps f, cert f r + k ≠ cert f t
  tmp : ∀ ν, ∀ I' ∈ honestInsts P fs H hdr (T.retemp P fs ν 0), ∀ f σ bufs kids,
    I'.t = .node f σ bufs kids → ∀ t ∈ P.temps f, ∀ q ∈ C I', q.1 = cert f t → q.2 = σ t
  keep : ∀ ν, ∀ I ∈ honestInsts P fs H hdr T, ∀ I' ∈ honestInsts P fs H hdr (T.retemp P fs ν 0),
    I'.fp = I.fp → I'.t = I.t.retemp P fs ν I.fp → ∀ q ∈ I'.cells C, ¬ TmpOff P cert I.t q.1 →
      q ∈ I.cells C

theorem read_some_gpow {κ : ℕ} (hκ : κ < 64) {M : MemImage κ} {a : K} {v : E} (h : M.read a = some v) :
    ∃ i : Fin (2 ^ κ), a = Parameters.gpow i :=
  let ⟨i, hi, _⟩ := (MemImage.read_eq_some_iff hκ M).mp h; ⟨i, hi⟩

/-- **Every equation names a word of the memory**. -/
theorem dischargeAddr {κ : ℕ} (hκ : κ < 64) {M : MemImage κ} {T : Tree} {args rets : List E}
    (hv : T.Valid P M.read args rets) (hp : T.Placed P fs cert 0)
    (hrun : ∀ I ∈ honestInsts P fs H hdr T, ∀ f σ bufs kids, I.t = .node f σ bufs kids →
      ∀ p r rs, Ev.atom (.frameAddr p (r :: rs)) ∈ I.t.events P →
        ∀ k < (r :: rs).length, I.fp + (cert f r + k) < 2 ^ κ) :
    ∀ q ∈ T.eqns P, ∃ i : Fin (2 ^ κ), q.1 = Parameters.gpow i := by
  intro q hq
  obtain ⟨I, hI, ⟨f, σ, bufs, kids, ht⟩, a, ha, hqa⟩ := eqns_insts (lp := P.loop) (H := H) T 0 hdr q hq
  have hgood := insts_good (H := H) T 0 hdr hv I hI
  obtain ⟨fn, es, vs, hf, hw, hes⟩ : ∃ fn es vs, P.find? f = some fn ∧ walk σ fn.body = .ret es vs ∧
      ∀ e ∈ es, e.Holds M.read σ := by
    rcases hgood with ⟨_, _, hv'⟩ | ⟨_, _, hph⟩
    · rw [ht] at hv'
      obtain ⟨fn, hf, _, es, vs, hw, _, hes, _⟩ := hv'
      exact ⟨fn, es, vs, hf, hw, hes⟩
    · rw [ht] at hph; cases hph
  have hev : I.t.events P = es := by rw [ht]; exact events_node hf hw
  have hval : I.t.val = σ := by rw [ht]; rfl
  rw [hval] at hqa
  have hh := hes _ (hev ▸ ha)
  cases a with
  | load d p off =>
    simp only [atomEqns, List.mem_singleton] at hqa
    subst hqa
    exact read_some_gpow hκ hh.2
  | rangeCheck x y t1 t2 k =>
    simp only [atomEqns, List.mem_cons, List.not_mem_nil, or_false] at hqa
    rcases hqa with rfl | rfl
    · exact read_some_gpow hκ hh.1.2
    · exact read_some_gpow hκ hh.2.2.2
  | frameAddr p run =>
    match run, hqa, ha with
    | r :: rs, hqa, ha =>
      simp only [atomEqns, List.mem_mapIdx] at hqa
      obtain ⟨k, hk, rfl⟩ := hqa
      have hpl := (Inst.nodeAt (insts_placedAt T 0 hdr hp I hI) (insts_placed T 0 hdr I hI) ht).2 (p, r)
        (List.mem_filterMap.mpr ⟨_, ha, rfl⟩)
      simp only at hpl
      rw [hpl, addr_ofK]
      have := hrun I hI f σ bufs kids ht p r rs ha k hk
      exact ⟨⟨_, by rw [← Nat.add_assoc] at this; exact this⟩, rfl⟩
  | _ => simp [atomEqns] at hqa

/-- **An honest tree of `main`** from its uniform placed relation at `0` on a consistent layout in
`[2, N)`, the header at words `0` and `1`, with the certificate's facts (`KFacts`). -/
theorem honest_of_relAtIn {N : ℕ} {L : Layout} (hcons : LConsistent L)
    (hin : ∀ q ∈ L, 2 ≤ q.1 ∧ q.1 + q.2.length ≤ N) (hN : N ≤ 2 ^ 32)
    (hrel : ∀ rd, LowDef 16 rd → MemL rd L → rd 1 = some hdr.1 → rd g = some hdr.2 →
      RelAtIn coreProgram fs cert rd (fun i => i < 2) (fun _ => False) 0 N "main" [] [])
    (hk : ∀ T : Tree, T.name = "main" → T.total fs = N → KFacts coreProgram fs cert H C hdr T) :
    ∃ (rd : Reader) (T : Tree), T.name = "main" ∧
      HonestAt coreProgram fs H C hdr T cert rd [] [] ∧ T.total fs = N := by
  have h16 : 16 ≤ logMem N := minLogMem_le_logMem N
  have h64 : logMem N < 64 := by have := logMem_le_maxLogMem hN; unfold maxLogMem at this; omega
  set M := imageOf (logMem N) L hdr with hM
  have hlow : LowDef 16 M.read := fun i hi => by
    have hi' : i < 2 ^ logMem N :=
      lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) h16)
    rw [MemImage.read_gpow h64 M ⟨i, hi'⟩]; rfl
  have hL := memL_imageOf h64 hcons (fun q hq => ⟨(hin q hq).1,
    le_trans (hin q hq).2 (le_two_pow_logMem N)⟩) hdr
  obtain ⟨hh0, hh1⟩ := imageOf_hdr h64 (by omega) L hdr
  have e0 : (1 : K) = Parameters.gpow 0 := by simp [Parameters.gpow]
  have e1 : g = Parameters.gpow 1 := by simp [Parameters.gpow]
  obtain ⟨t, hn, hv, hb, hp, ht, hl, -⟩ := hrel M.read hlow hL (by rw [e0]; exact hh0)
    (by rw [e1]; exact hh1)
  subst ht
  have hkf := hk t hn rfl
  have hd : DischargeHyps coreProgram fs cert H C hdr t (fun i => i < 2) M [] [] :=
    { fresh := coreProgram_fresh
      valid := hv
      bufsOk := hb
      placed := hp
      loads := hl
      region := fun i hi => Or.inl hi
      hdr_read := ⟨hh0, hh1⟩
      size := hN
      addr := dischargeAddr h64 hv hp fun I hI f σ bufs kids hIt p r rs ha k hk' => by
        have hc := (hkf.run I hI f σ bufs kids hIt p r rs ha k hk').1
        have hoff := (hkf.cells.off I hI _ hc).2
        have hw := honest_within (P := coreProgram) hI (by have := hkf.cells.two_le I hI; omega)
        have := le_two_pow_logMem (t.total fs)
        omega
      cells := hkf.cells
      cells' := hkf.cells'
      cert_lt := hkf.cert_lt
      cert_inj := hkf.cert_inj
      run := hkf.run
      tmp := hkf.tmp
      keep := hkf.keep }
  obtain ⟨ν, hν⟩ := honestAt_retemp hd
  exact ⟨_, _, by rw [name_retemp]; exact hn, hν, total_retemp t 0⟩

/-- **`main`'s honest tree from `main_complete`'s form at `0`**: its layout after `main`'s frame,
consistent, its size at most `2^32`. -/
theorem honest_of_complete {m : ℕ} {L : Layout} (hfs : 2 ≤ fs "main")
    (hW : LeanVM.Guest.B1.Within L (0 + fs "main") m) (hcons : LConsistent L)
    (hN : fs "main" + m ≤ 2 ^ 32)
    (hrel : ∀ rd, LowDef 16 rd → MemL rd L → rd 1 = some hdr.1 → rd g = some hdr.2 →
      RelAtIn coreProgram fs cert rd (fun i => i < 2) (fun _ => False) 0 (fs "main" + m) "main" [] [])
    (hk : ∀ T : Tree, T.name = "main" → T.total fs = fs "main" + m →
      KFacts coreProgram fs cert H C hdr T) :
    ∃ (rd : Reader) (T : Tree), T.name = "main" ∧
      HonestAt coreProgram fs H C hdr T cert rd [] [] ∧ T.total fs = fs "main" + m :=
  honest_of_relAtIn hcons (fun q hq => by have := hW q hq; omega) hN hrel hk

end
end LeanVM.Guest.B1.Main
