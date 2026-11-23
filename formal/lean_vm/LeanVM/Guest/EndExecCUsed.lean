/-
  LeanVM.Guest.EndExecCUsed

  The cells a hint writes: a hint whose destinations and reservation are below `B`, run from a
  memory using at most `B` cells, leaves it so.
-/

module

public import LeanVM.Guest.EndExecX
public import LeanVM.Guest.Bridge.AllocCells

/-!
# The cells a hint writes

`UsedOk B s h`: the cells hint `h` writes from state `s` are below `B`: its frame cells (a pointer
cell, a cell's address, a stack run, a destination cell), the runs from a buffer pointer it reads
(`PtrAt`), and the cells an allocation reserves from the bump pointer, of the size it reads.
`usedOk_run`: a hint run from `s.mem.used ≤ B` under `UsedOk B` keeps `used ≤ B` (`put_used`,
`Mem.ensure_used`); `hints_used`: so does a list of hints, each under `UsedOk B` at the state the
ones before it reach.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Prover.Exec

@[expose] public section

/-- A run of `n` cells `pos` past a destination below `B`: from the frame's cell, or from the
buffer the pointer cell names. -/
def DstB (B : ℕ) (s : St) : BitsDest → ℕ → ℕ → Prop
  | .stack base, pos, n => ∀ k < n, s.fp + base + pos + k < B
  | .heap ptr, pos, n => ∀ b, PtrAt s (s.fp + ptr) b → ∀ k < n, b + pos + k < B

/-- **The cells hint `h` writes from `s` are below `B`.** -/
def UsedOk (B : ℕ) (s : St) : Hint → Prop
  | .frameAddress _ => True
  | .alloc p n => s.fp + p < B ∧ s.nextFree + n ≤ B
  | .allocDyn p c => s.fp + p < B ∧ ∀ n, PtrAt s (s.fp + c) n → s.nextFree + n ≤ B
  | .allocArm p sel sizes => s.fp + p < B ∧
      ∀ k n, PtrAt s (s.fp + sel) k → sizes[k]? = some n → s.nextFree + n ≤ B
  | .cellAddress p _ => s.fp + p < B
  | .allocFrames p size stop si tail => s.fp + p < B ∧
      ∀ v n, n < maxCells → s.mem.peek (s.fp + stop) = ofK v → v * si = Parameters.g ^ n →
        s.nextFree + (size * n + tail) ≤ B
  | .witnessStack _ base len => ∀ k < len, s.fp + base + k < B
  | .witnessHeap _ ptr lo len => ∀ b, PtrAt s (s.fp + ptr) b → ∀ k < len, b + lo + k < B
  | .log2Ceil _ dst _ _ => s.fp + dst < B
  | .bitDecompose _ d n => DstB B s d 0 n
  | .bitDecomposeExp _ d n => DstB B s d 0 n
  | .windowsExp _ d pos _ _ count => DstB B s d pos count
  | .digitDecomposeExp _ d _ ndigits _ _ _ => DstB B s d 0 ndigits
  | .fieldLimbs _ base len => ∀ k < len, s.fp + base + k < B
  | .inverse _ dst => s.fp + dst < B

/-- **The runs from a buffer pointer hint `h` writes from `s` are below `B`.** -/
def HeapB (B : ℕ) (s : St) : Hint → Prop
  | .witnessHeap _ ptr lo len => ∀ b, PtrAt s (s.fp + ptr) b → ∀ k < len, b + lo + k < B
  | .bitDecompose _ (.heap ptr) n | .bitDecomposeExp _ (.heap ptr) n =>
      ∀ b, PtrAt s (s.fp + ptr) b → ∀ k < n, b + 0 + k < B
  | .windowsExp _ (.heap ptr) pos _ _ count => ∀ b, PtrAt s (s.fp + ptr) b → ∀ k < count, b + pos + k < B
  | .digitDecomposeExp _ (.heap ptr) _ ndigits _ _ _ => ∀ b, PtrAt s (s.fp + ptr) b → ∀ k < ndigits, b + 0 + k < B
  | _ => True

/-- **The cells allocation hint `h` reserves from `s` are below `B`**, of the size it reads. -/
def AllocB (B : ℕ) (s : St) : Hint → Prop
  | .alloc _ n => s.nextFree + n ≤ B
  | .allocDyn _ c => ∀ n, PtrAt s (s.fp + c) n → s.nextFree + n ≤ B
  | .allocArm _ sel sizes => ∀ k n, PtrAt s (s.fp + sel) k → sizes[k]? = some n → s.nextFree + n ≤ B
  | .allocFrames _ size stop si tail => ∀ v n, n < maxCells → s.mem.peek (s.fp + stop) = ofK v →
      v * si = Parameters.g ^ n → s.nextFree + (size * n + tail) ≤ B
  | _ => True

end

public section

/-! ## The reference's words -/

/-- **A state the hints reach agrees with the reference**: the same frame, its written cells the
reference's words (what `Moves` gives and the hint facts read). -/
abbrev MovesW (M : ℕ → E) (s s' : St) : Prop := s'.fp = s.fp ∧ ∀ c v, s'.mem.get c = some v → M c = v

theorem _root_.LeanVM.Prover.Exec.Moves.w {M : ℕ → E} {s s' : St} (h : Moves M s s') : MovesW M s s' := ⟨h.fp, h.fine.agree.get⟩

/-- **A word the reference holds at `g^c` is its cell `c`'s, below `2^κ`.** -/
theorem refRd_imgK {κ : ℕ} (hκ : κ ≤ 28) (img : MemoryImage κ) {c : ℕ} {v : E} (hc : c < 2 ^ 62)
    (h : img.read (Parameters.g ^ c) = some v) : c < 2 ^ κ ∧ refMem img c = v := by
  obtain ⟨i, hi, hv⟩ := (MemoryImage.read_eq_some_iff (by omega) img).mp h
  have hi' : (i : ℕ) < 2 ^ 28 := lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) hκ)
  have hci : c = i := gpow_inj (by omega) (by omega) hi
  subst hci
  refine ⟨i.isLt, ?_⟩
  unfold refMem
  rw [dite_eq_left i.isLt, ← hv]

/-- A pointer cell holding a power is written. -/
theorem get_of_ptrAt {s : St} {c b : ℕ} (h : PtrAt s c b) : ∃ v, s.mem.get c = some v ∧ v = ofK (Parameters.g ^ b) := by
  unfold PtrAt Mem.peek at h
  cases hg : s.mem.get c with
  | none => rw [hg] at h; exact absurd h.1.symm (Mode.ofK_gpow_ne_zero b)
  | some v => rw [hg] at h; exact ⟨v, rfl, h.1⟩

/-! ## Steps that keep the memory -/

/-- The same memory, frame and bump pointer. -/
def Sm (s s' : St) : Prop := s'.mem = s.mem ∧ s'.fp = s.fp ∧ s'.nextFree = s.nextFree

theorem Sm.refl (s : St) : Sm s s := ⟨rfl, rfl, rfl⟩

theorem Sm.trans {a b c : St} (h1 : Sm a b) (h2 : Sm b c) : Sm a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem PtrAt.sm {s s' : St} (h : Sm s s') {c b : ℕ} (hp : PtrAt s c b) : PtrAt s' c b := by
  unfold PtrAt Mem.peek at *; rw [h.1]; exact hp

theorem logOr_sm {s s' : St} {x : K} {b k : ℕ} {f : Fault} (hs : s.Good) (h : s.logOr x b f = .ok (k, s')) :
    Sm s s' ∧ Parameters.g ^ k = x ∧ k < b := by
  obtain ⟨-, h2⟩ := St.logOr_ok hs h
  obtain ⟨D, rfl⟩ := St.logOr_dl h
  exact ⟨⟨rfl, rfl, rfl⟩, h2⟩


theorem pop_sm {C : Ctx} {s s' : St} {name : String} {len : ℕ} {v : List E} (h : pop C s name len = .ok (v, s')) :
    Sm s s' ∧ v.length = len := by
  unfold pop at h
  split at h
  · dsimp only at h
    split at h
    · split_ifs at h with hl
      · cases h
      · simp only [pure_ok, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨⟨rfl, rfl, rfl⟩, not_not.mp hl⟩
    · simp at h
  · simp at h

theorem ptrAt_of {s : St} {c : ℕ} {p : K} {b : ℕ} {what : String} (h1 : inK what (s.mem.peek c) = .ok p)
    (h2 : Parameters.g ^ b = p) (h3 : b < maxCells) : PtrAt s c b := by
  obtain ⟨hl, rfl⟩ := inK_ok h1
  refine ⟨E.ext fun i ↦ ?_, h3⟩
  fin_cases i
  · simp [h2]
  · simpa using hl

theorem heapBase_sm {s s' : St} {c b : ℕ} {what : String} (hs : s.Good) (h : heapBase s c what = .ok (b, s')) :
    Sm s s' ∧ PtrAt s c b := by
  unfold heapBase at h
  rw [bind_ok] at h
  obtain ⟨p, hp, h⟩ := h
  obtain ⟨hsm, h2, h3⟩ := logOr_sm hs h
  exact ⟨hsm, ptrAt_of hp h2 h3⟩

theorem bitsBase_sm {B : ℕ} {s s' : St} {d : BitsDest} {len : ℕ} {what : String} {b : ℕ} (hs : s.Good)
    (h : bitsBase s d len what = .ok (b, s')) :
    Sm s s' ∧ ∀ pos n, DstB B s d pos n → ∀ k < n, b + pos + k < B := by
  cases d with
  | stack base =>
    simp only [bitsBase, bind_ok, pure_ok, Prod.mk.injEq] at h
    obtain ⟨c, hc, rfl, rfl⟩ := h
    obtain ⟨rfl, -⟩ := runAt_ok hc
    exact ⟨Sm.refl _, fun _ _ hn ↦ hn⟩
  | heap ptr =>
    simp only [bitsBase, bind_ok, pure_ok, Prod.mk.injEq] at h
    obtain ⟨c, hc, ⟨b', s2⟩, h1, c2, hc2, hb, hs2⟩ := h
    subst hb hs2
    obtain ⟨rfl, -⟩ := cellAt_ok hc
    obtain ⟨rfl, -⟩ := runAt_ok hc2
    obtain ⟨hsm, hp⟩ := heapBase_sm hs h1
    exact ⟨hsm, fun _ _ hn ↦ by simpa using hn _ hp⟩


theorem withMem_used {s s' : St} {f : Mem → Except Fault Mem} (h : s.withMem f = .ok s') :
    ∃ m, f s.mem = .ok m ∧ s'.mem = m ∧ s'.fp = s.fp ∧ s'.nextFree = s.nextFree := by
  obtain ⟨m, hm, rfl⟩ := St.withMem_ok h
  exact ⟨m, hm, rfl, rfl, rfl⟩

theorem putRun_used {B b : ℕ} : ∀ (vs : List E) (k : ℕ) (m m' : Mem),
    (vs.zipIdx k).foldlM (fun m (x : E × ℕ) ↦ m.put (b + x.2) x.1) m = .ok m' → m.used ≤ B →
      (∀ i < vs.length, b + k + i < B) → m'.used ≤ B
  | [], _, m, m', e, h, _ => by simp only [List.zipIdx_nil, List.foldlM_nil, pure_ok] at e; subst e; exact h
  | v :: vs, k, m, m', e, h, hb => by
    rw [List.zipIdx_cons, List.foldlM_cons, bind_ok] at e
    obtain ⟨m1, e1, e⟩ := e
    refine putRun_used vs (k + 1) m1 m' e ?_ fun i hi ↦ ?_
    · rw [put_used e1]
      have := hb 0 (by simp)
      omega
    · have := hb (i + 1) (by simp; omega)
      omega

theorem putRun_used' {B b : ℕ} {vs : List E} {m m' : Mem} (e : putRun b vs m = .ok m') (h : m.used ≤ B)
    (hb : ∀ i < vs.length, b + i < B) : m'.used ≤ B :=
  putRun_used vs 0 m m' e h (by simpa using hb)

theorem withRun_used {B b : ℕ} {vs : List E} {s s' : St} (e : s.withMem (putRun b vs) = .ok s') (h : s.mem.used ≤ B)
    (hb : ∀ i < vs.length, b + i < B) : s'.mem.used ≤ B := by
  obtain ⟨m, hm, h1, -⟩ := withMem_used e
  rw [h1]; exact putRun_used' hm h hb

theorem withPut_used {B c : ℕ} {v : E} {s s' : St} (e : s.withMem (·.put c v) = .ok s') (h : s.mem.used ≤ B)
    (hc : c < B) : s'.mem.used ≤ B := by
  obtain ⟨m, hm, h1, -⟩ := withMem_used e
  rw [h1, put_used hm]; omega

theorem allocate_used {B p n : ℕ} {s s' : St} (e : allocate s p n = .ok s') (h : s.mem.used ≤ B)
    (hp : s.fp + p < B) (hn : s.nextFree + n ≤ B) : s'.mem.used ≤ B := by
  unfold allocate at e
  rw [bind_ok] at e
  obtain ⟨cell, hcell, e⟩ := e
  obtain ⟨rfl, -⟩ := cellAt_ok hcell
  dsimp only at e
  split at e
  · cases e
  · rw [bind_ok] at e
    obtain ⟨s1, h1, e⟩ := e
    simp only [pure_ok] at e; subst e
    obtain ⟨m, hm, hm1, -⟩ := withMem_used h1
    show s1.mem.used ≤ B
    rw [hm1, put_used hm]
    split_ifs <;> simp <;> omega

/-- **A hint whose writes are below `B` keeps the memory's cells used below `B`.** -/
theorem usedOk_run {B : ℕ} {C : Ctx} {s s' : St} {h : Hint} (hs : s.Good) (e : runHint C s h = .ok s')
    (hu : UsedOk B s h) (h0 : s.mem.used ≤ B) : s'.mem.used ≤ B := by
  cases h with
  | frameAddress o =>
    simp only [runHint, bind_ok, pure_ok] at e
    obtain ⟨c, -, rfl⟩ := e
    exact h0
  | alloc p n => exact allocate_used e h0 hu.1 hu.2
  | allocDyn p c =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, hc, sz, hsz, ⟨n, s1⟩, h1, e⟩ := e
    obtain ⟨rfl, -⟩ := cellAt_ok hc
    obtain ⟨hsm, h2, h3⟩ := logOr_sm hs h1
    rw [← hsm.1] at h0
    exact allocate_used e h0 (by rw [hsm.2.1]; exact hu.1)
      (by rw [hsm.2.2]; exact hu.2 n (ptrAt_of hsz h2 h3))
  | allocArm p sel sizes =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, hc, x, hx, ⟨k, s1⟩, h1, e⟩ := e
    obtain ⟨rfl, -⟩ := cellAt_ok hc
    obtain ⟨hsm, h2, h3⟩ := logOr_sm hs h1
    split at e
    · rename_i n hn
      rw [← hsm.1] at h0
      exact allocate_used e h0 (by rw [hsm.2.1]; exact hu.1) (by rw [hsm.2.2]; exact hu.2 k n (ptrAt_of hx h2 h3) hn)
    · simp at e
  | cellAddress p c =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c', -, pc, hpc, e⟩ := e
    obtain ⟨rfl, -⟩ := cellAt_ok hpc
    exact withPut_used e h0 hu
  | allocFrames p size stop si tail =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, hc, sp, hsp, e⟩ := e
    obtain ⟨rfl, -⟩ := cellAt_ok hc
    split_ifs at e
    · simp [bind_ok] at e
    · rw [bind_ok] at e
      obtain ⟨⟨n, s1⟩, h1, e⟩ := e
      obtain ⟨hsm, h2, h3⟩ := logOr_sm hs h1
      obtain ⟨hl, rfl⟩ := inK_ok hsp
      rw [← hsm.1] at h0
      have hpk : s.mem.peek (s.fp + stop) = ofK ((s.mem.peek (s.fp + stop)).limb 0) :=
        E.ext fun i ↦ by fin_cases i <;> simp [hl]
      exact allocate_used e h0 (by rw [hsm.2.1]; exact hu.1) (by rw [hsm.2.2]; exact hu.2 _ n h3 hpk h2.symm)
  | witnessStack S base len =>
    simp only [runHint, bind_ok] at e
    obtain ⟨bs, hbs, ⟨v, s1⟩, h1, e⟩ := e
    obtain ⟨rfl, -⟩ := runAt_ok hbs
    obtain ⟨hsm, hl⟩ := pop_sm h1
    rw [← hsm.1] at h0
    exact withRun_used e h0 (by rw [hl]; exact hu)
  | witnessHeap S ptr lo len =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, hc, ⟨b, s1⟩, h1, bl, hbl, ⟨v, s2⟩, h2, e⟩ := e
    obtain ⟨rfl, -⟩ := cellAt_ok hc
    obtain ⟨rfl, -⟩ := runAt_ok hbl
    obtain ⟨hsm1, hp⟩ := heapBase_sm hs h1
    obtain ⟨hsm2, hl⟩ := pop_sm h2
    rw [← (hsm1.trans hsm2).1] at h0
    exact withRun_used e h0 (by rw [hl]; exact hu b hp)
  | log2Ceil bits dst nbits floor =>
    simp only [runHint, bind_ok] at e
    obtain ⟨⟨b, s1⟩, h1, dc, hdc, e⟩ := e
    obtain ⟨rfl, -⟩ := cellAt_ok hdc
    obtain ⟨hsm, -⟩ := bitsBase_sm (B := B) hs h1
    rw [← hsm.1] at h0
    exact withPut_used e h0 (by rw [hsm.2.1]; exact hu)
  | bitDecompose value bits nbits =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, ⟨b, s1⟩, h1, e⟩ := e
    obtain ⟨hsm, hd⟩ := bitsBase_sm (B := B) hs h1
    rw [← hsm.1] at h0
    exact withRun_used e h0 (by simpa using hd 0 nbits hu)
  | bitDecomposeExp value bits nbits =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, n, -, ⟨b, s1⟩, h1, e⟩ := e
    obtain ⟨hsm, hd⟩ := bitsBase_sm (B := B) hs h1
    rw [← hsm.1] at h0
    exact withRun_used e h0 (by simpa using hd 0 nbits hu)
  | windowsExp value dest pos start width count =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, ⟨b, s1⟩, h1, e⟩ := e
    obtain ⟨hsm, hd⟩ := bitsBase_sm (B := B) hs h1
    rw [← hsm.1] at h0
    exact withRun_used e h0 (by simpa using hd pos count hu)
  | digitDecomposeExp value dst nbits ndigits digitBits start startCell =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, n, -, e⟩ := e
    obtain ⟨⟨b, s1⟩, h1, e⟩ : ∃ x : ℕ × St, bitsBase s dst ndigits "hint_decompose_digits_exponent pointer" = .ok x ∧
        ∃ st, x.2.withMem (putRun x.1 ((List.range ndigits).map fun j ↦ ofK (Parameters.g ^
          (if 128 ≤ st + digitBits * j then 0 else (n >>> (st + digitBits * j)) % 2 ^ digitBits)))) = .ok s' := by
      cases startCell with
      | none =>
        simp only [pure_bind] at e
        rw [bind_ok] at e
        obtain ⟨x, hx, e⟩ := e
        exact ⟨x, hx, start, e⟩
      | some c =>
        rw [bind_ok] at e
        obtain ⟨l, -, e⟩ := e
        rw [bind_ok] at e
        obtain ⟨st, -, e⟩ := e
        rw [bind_ok] at e
        obtain ⟨x, hx, e⟩ := e
        exact ⟨x, hx, st, e⟩
    obtain ⟨st, e⟩ := e
    obtain ⟨hsm, hd⟩ := bitsBase_sm (B := B) hs h1
    rw [← hsm.1] at h0
    exact withRun_used e h0 (by simpa using hd 0 ndigits hu)
  | fieldLimbs value base len =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, bs, hbs, e⟩ := e
    obtain ⟨rfl, -⟩ := runAt_ok hbs
    exact withRun_used e h0 (by simp only [List.length_map, List.length_range]; exact hu)
  | inverse value dst =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, dc, hdc, e⟩ := e
    obtain ⟨rfl, -⟩ := cellAt_ok hdc
    exact withPut_used e h0 hu

/-! ## By parts -/

/-- **A hint's writes below `B`**: its frame cells within a frame ending at `B`, its runs from a
pointer and its reservation below `B`. -/
theorem usedOk_of {B fs : ℕ} {s : St} {h : Hint} (hc : Bridge.hintCellsOk fs h = true)
    (hfs : s.fp + fs ≤ B) (hH : HeapB B s h) (hA : AllocB B s h) : UsedOk B s h := by
  have hd : ∀ (d : BitsDest) (pos n : ℕ), Bridge.dstCellsOk fs d (pos + n) = true →
      (∀ ptr, d = .heap ptr → ∀ b, PtrAt s (s.fp + ptr) b → ∀ k < n, b + pos + k < B) → DstB B s d pos n := by
    intro d pos n hc' hh
    cases d with
    | stack base => simp only [Bridge.dstCellsOk, decide_eq_true_eq] at hc'; intro k hk; omega
    | heap ptr => exact hh ptr rfl
  cases h with
  | bitDecompose v d n => exact hd d 0 n (by rw [Nat.zero_add]; exact hc) fun ptr h ↦ by subst h; exact hH
  | bitDecomposeExp v d n => exact hd d 0 n (by rw [Nat.zero_add]; exact hc) fun ptr h ↦ by subst h; exact hH
  | windowsExp v d pos st w count => exact hd d pos count hc fun ptr h ↦ by subst h; exact hH
  | digitDecomposeExp v d nb nd db st sc => exact hd d 0 nd (by rw [Nat.zero_add]; exact hc) fun ptr h ↦ by subst h; exact hH
  | witnessHeap => exact hH
  | frameAddress => trivial
  | witnessStack _ base len =>
    simp only [Bridge.hintCellsOk, decide_eq_true_eq] at hc
    intro k hk; omega
  | fieldLimbs _ base len =>
    simp only [Bridge.hintCellsOk, decide_eq_true_eq] at hc
    intro k hk; omega
  | _ =>
    simp only [Bridge.hintCellsOk, decide_eq_true_eq] at hc
    first
    | exact ⟨by omega, hA⟩
    | (show _ < B; omega)

theorem ptrAt_uniq {s : St} {c a b : ℕ} (ha : PtrAt s c a) (hb : PtrAt s c b) : a = b :=
  gpow_inj (by have := ha.2; unfold maxCells at this; omega) (by have := hb.2; unfold maxCells at this; omega)
    (ofK_injective (ha.1.symm.trans hb.1))

/-! ## The allocations' reservations -/

theorem allocB_dyn {B : ℕ} {s : St} {p c n : ℕ} (hp : PtrAt s (s.fp + c) n) (hb : s.nextFree + n ≤ B) :
    AllocB B s (.allocDyn p c) := fun n' hp' ↦ by rw [← ptrAt_uniq hp hp']; exact hb

theorem allocB_arm {B : ℕ} {s : St} {p sel k n : ℕ} {sizes : List ℕ} (hp : PtrAt s (s.fp + sel) k)
    (hk : sizes[k]? = some n) (hb : s.nextFree + n ≤ B) : AllocB B s (.allocArm p sel sizes) :=
  fun k' n' hp' hk' ↦ by
    rw [← ptrAt_uniq hp hp', hk] at hk'
    rw [← Option.some.inj hk']; exact hb

theorem allocB_frames {B : ℕ} {s : St} {p size stop n tail : ℕ} {v si : K}
    (hp : s.mem.peek (s.fp + stop) = ofK v) (hv : v * si = Parameters.g ^ n) (hn : n < maxCells)
    (hb : s.nextFree + (size * n + tail) ≤ B) : AllocB B s (.allocFrames p size stop si tail) :=
  fun v' n' hn' hp' hv' ↦ by
    obtain rfl : v' = v := ofK_injective (hp'.symm.trans hp)
    obtain rfl : n' = n := gpow_inj (by unfold maxCells at hn'; omega) (by unfold maxCells at hn; omega)
      (hv'.symm.trans hv)
    exact hb

/-- **A list of hints each writing below `B`** keeps the memory's cells used below `B`. -/
theorem hints_used {B : ℕ} {C : Ctx} :
    ∀ (l : List Hint) (s s1 : St), s.Good → l.foldlM (runHint C) s = .ok s1 → s.mem.used ≤ B →
      (∀ i h sx, l[i]? = some h → (l.take i).foldlM (runHint C) s = .ok sx → UsedOk B sx h) → s1.mem.used ≤ B
  | [], s, s1, _, e, h0, _ => by simp only [List.foldlM_nil, pure_ok] at e; subst e; exact h0
  | x :: l, s, s1, hs, e, h0, hu => by
    rw [List.foldlM_cons, bind_ok] at e
    obtain ⟨s2, e2, e⟩ := e
    have hx := hu 0 x s rfl rfl
    have hs2 := (runHint_follows hs e2).good
    refine hints_used l s2 s1 hs2 e (usedOk_run hs e2 hx h0) fun i h sx hi hx' ↦ ?_
    refine hu (i + 1) h sx (by simpa using hi) ?_
    rw [List.take_succ_cons, List.foldlM_cons, bind_ok]
    exact ⟨s2, e2, hx'⟩

end

end LeanVM.Guest.EndExec
