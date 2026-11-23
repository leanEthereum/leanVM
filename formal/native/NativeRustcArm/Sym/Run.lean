module

public import NativeRustcArm.Sym.Simp
public import NativeRustcArm.Spec.Mem

/-!
# Function proofs with the symbolic executor

The glue a function proof uses around `Sym.exec_sound`:
- running a block from a machine state and continuing (`exec_then`, `exec_at`);
- a fresh environment and symbolic state for a machine state (`match_ofMachine`), its hypotheses
  stated on the lists `init` takes (`List.Forall`, `List.Forall₂`);
- a call: the callee's contract from the `bl`'s exit (`call_then`);
- a loop: an invariant with a measure (`loop`);
- memory after a block: a write's bytes (`Match.bytesAt_write`, `findWrite_head`), the bytes no
  write covers (`Match.get?_mem0`, `Match.sameOutside`), the environment's loads
  (`Env.load_of_bytesAt`);
- the registers a block keeps (`Match.reg_eq`, `Match.saved`, `Saved.trans`).
-/

namespace NativeRustcArm.Sym

open NativeRustcArm

public section

/-! ## Loops -/

/-- **A loop**: from a state satisfying the invariant `I n`, each iteration inevitably reaches
the exit `Q` or the invariant with a smaller measure. -/
theorem loop {σ : Type} {tr : σ → (σ → Prop) → Prop} {Q : σ → Prop} (I : Nat → σ → Prop)
    (step : ∀ n s, I n s → Eventually tr (fun s' => Q s' ∨ ∃ n' < n, I n' s') s) :
    ∀ {n : Nat} {s : σ}, I n s → Eventually tr Q s := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro s h
    exact eventually_trans _ _ _ _ (step n s h) fun s' h' => by
      rcases h' with hq | ⟨n', hn', hi⟩
      · exact .done _ hq
      · exact ih n' hn' hi

/-! ## Blocks and calls -/

section
variable [Host] {env : Env}

/-- A block run from `m` at its address, then `cont` from where it ends. -/
theorem exec_then {ds : List Directive} {k : Nat} {S S' : SState} {x : Exit} {m : MachineData}
    {R : MachineState → Prop} (hk : ds.IsInfixAt Host.prog k) (hx : exec ds S = some (S', x))
    (hwf : env.WF) (hm : Match env S m)
    (cont : ∀ st, Match env S' st.data → PcOk env x (Host.addrOf (k + ds.length)) st →
      Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf k⟩ :=
  eventually_trans _ _ _ _ (exec_sound hk hx hwf hm) fun st h => cont st h.1 h.2

/-- `exec_then` from a machine state at the block's address. -/
theorem exec_at {ds : List Directive} {k : Nat} {S S' : SState} {x : Exit} {st : MachineState}
    {R : MachineState → Prop} (hk : ds.IsInfixAt Host.prog k) (hx : exec ds S = some (S', x))
    (hwf : env.WF) (hpc : st.pc = Host.addrOf k) (hm : Match env S st.data)
    (cont : ∀ st', Match env S' st'.data → PcOk env x (Host.addrOf (k + ds.length)) st' →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  obtain ⟨m, pc⟩ := st
  cases hpc
  exact exec_then hk hx hwf hm cont

/-- **A call**: where a block ends in `bl l`, the callee's contract takes the machine to the
return address, and `cont` from there. -/
theorem call_then {l : Label} {next : Int64} {st : MachineState} {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} {R : MachineState → Prop}
    (hpc : PcOk env (.call l) next st) (hspec : Spec (Labels.label l) P Q) (hP : P st.data)
    (cont : ∀ st', st'.pc = next → Q st.data st'.data → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st :=
  Eventually.bind (Spec.apply hspec hpc.1 hP) fun st' h => cont st' (h.1.trans hpc.2) h.2

end

/-! ## A fresh environment -/

theorem XReg.eq_of_beq {a b : XReg} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- `P` holds of every element (a conjunction, for literal lists). -/
@[expose] def AllOf {α : Type} (P : α → Prop) : List α → Prop
  | [] => True
  | a :: l => P a ∧ AllOf P l

/-- The symbolic regions (sizes, alignment flags) are the environment's. -/
@[expose] def RegionsOk : List (Nat × Bool) → List (BitVec 64 × Nat) → Prop
  | [], _ => True
  | (n, al) :: ss, (b, n') :: es => n = n' ∧ (al = true → b.toNat % 16 = 0) ∧ RegionsOk ss es
  | _ :: _, [] => False

theorem lookup_of_allOf {α β : Type} [BEq α] {P : α → β → Prop}
    (heq : ∀ a b : α, (a == b) = true → a = b) {l : List (α × β)}
    (hl : AllOf (fun p => P p.1 p.2) l) {a : α} {b : β} (h : l.lookup a = some b) : P a b := by
  induction l with
  | nil => cases h
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    unfold List.lookup at h
    split at h
    · rename_i ha
      cases h
      rw [heq a k ha]
      exact hl.1
    · exact ih hl.2 h

theorem mem_of_allOf {α : Type} {P : α → Prop} {l : List α} (hl : AllOf P l) {a : α}
    (h : a ∈ l) : P a := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact hl.1
    · exact ih hl.2 h

theorem regionsOk_getElem? {ss : List (Nat × Bool)} {es : List (BitVec 64 × Nat)}
    (h : RegionsOk ss es) {i n : Nat} {al : Bool} (hi : ss[i]? = some (n, al)) :
    ∃ b : BitVec 64, es[i]? = some (b, n) ∧ (al = true → b.toNat % 16 = 0) := by
  induction ss generalizing es i with
  | nil => cases hi
  | cons s ss ih =>
    obtain ⟨n₁, al₁⟩ := s
    cases es with
    | nil => exact h.elim
    | cons e es =>
      obtain ⟨b, n'⟩ := e
      obtain ⟨hn, hal, h⟩ := h
      cases i with
      | zero =>
        cases hi
        subst hn
        exact ⟨b, rfl, hal⟩
      | succ i => exact ih h hi

/-- **A fresh environment for a machine state**: `Env.ofMachine m regions` and the symbolic state
`init sregions sp₀ known labels bounds aliases` describe `m` when the symbolic regions are the
environment's (sizes, and 16-byte aligned bases where flagged), SP and the `known` registers are
their symbolic values, and the labels, bounds and aliases hold. -/
theorem match_ofMachine [Labels] {m : MachineData} {regions : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {sregions : List (Nat × Bool)} {sp₀ : Sym} {known : List (XReg × Sym)}
    {labels : List (Label × Nat)} {bounds : List (Sym × Nat)} {aliases : List (Sym × Nat × Int)}
    (hregions : RegionsOk sregions regions)
    (hsp : m.regs.SP.toBitVec = sp₀.eval (Env.ofMachine m regions vars))
    (hknown : AllOf (fun p =>
      (m.regs.getXReg p.1).toBitVec = p.2.eval (Env.ofMachine m regions vars)) known)
    (hlabels : AllOf (fun p =>
      (Env.ofMachine m regions vars).base p.2 = (Labels.label p.1).toBitVec) labels)
    (hbounds : AllOf (fun p => (p.1.eval (Env.ofMachine m regions vars)).toNat < p.2) bounds)
    (haliases : AllOf (fun p => p.1.eval (Env.ofMachine m regions vars) =
      (Env.ofMachine m regions vars).base p.2.1 + BitVec.ofInt 64 p.2.2) aliases) :
    Match (Env.ofMachine m regions vars) (init sregions sp₀ known labels bounds aliases) m :=
  match_init (fun _ _ => rfl)
    (fun r v h => lookup_of_allOf (P := fun r v =>
      (m.regs.getXReg r).toBitVec = v.eval (Env.ofMachine m regions vars))
      (fun _ _ => XReg.eq_of_beq) hknown h)
    hsp rfl
    (fun r n al h => regionsOk_getElem? hregions h)
    (fun l r h => lookup_of_allOf (P := fun l r =>
      (Env.ofMachine m regions vars).base r = (Labels.label l).toBitVec)
      (fun _ _ h => by simpa using h) hlabels h)
    (fun x n h => mem_of_allOf (P := fun p : Sym × Nat =>
      (p.1.eval (Env.ofMachine m regions vars)).toNat < p.2) hbounds h)
    (fun x r o h => lookup_of_allOf (P := fun x (ro : Nat × Int) =>
      x.eval (Env.ofMachine m regions vars) = (Env.ofMachine m regions vars).base ro.1 +
        BitVec.ofInt 64 ro.2) (fun _ _ h => by simpa using h) haliases h)
    rfl

/-- The environment of a machine state without regions is well formed. -/
theorem Env.wf_nil (m : MachineData) (vars : Nat → BitVec 64 := fun _ => 0) :
    (Env.ofMachine m [] vars).WF where
  noWrap _ _ _ h := by cases h
  mapped _ _ _ h := by cases h
  disjoint _ _ _ _ _ _ _ h := by cases h

/-- A machine state without regions, every register its atom. -/
theorem match_nil [Labels] (m : MachineData) : Match (Env.ofMachine m []) (init [] .sp) m :=
  match_ofMachine trivial rfl trivial trivial trivial trivial

@[simp] theorem Env.ofMachine_regs (m : MachineData) (regions : List (BitVec 64 × Nat))
    (vars : Nat → BitVec 64) (r : XReg) :
    (Env.ofMachine m regions vars).regs r = (m.regs.getXReg r).toBitVec := rfl

@[simp] theorem Env.ofMachine_mem0 (m : MachineData) (regions : List (BitVec 64 × Nat))
    (vars : Nat → BitVec 64) : (Env.ofMachine m regions vars).mem0 = m.dmem := rfl

@[simp] theorem Env.ofMachine_regions (m : MachineData) (regions : List (BitVec 64 × Nat))
    (vars : Nat → BitVec 64) : (Env.ofMachine m regions vars).regions = regions := rfl

@[simp] theorem Env.base_ofMachine_eq (m : MachineData) (regions : List (BitVec 64 × Nat))
    (vars : Nat → BitVec 64) (r : Nat) :
    (Env.ofMachine m regions vars).base r = ((regions[r]?).map (·.1)).getD 0 := rfl

theorem Env.base_ofMachine (m : MachineData) (regions : List (BitVec 64 × Nat))
    (vars : Nat → BitVec 64) {r : Nat} {b : BitVec 64} {n : Nat}
    (h : regions[r]? = some (b, n)) : (Env.ofMachine m regions vars).base r = b :=
  Env.base_eq h

/-! ## Memory after a block -/

variable [Labels] {env : Env} {S : SState} {m : MachineData}

omit [Labels] in
/-- The environment's `n` bytes at `off` in region `r`, when they are `bs`. -/
theorem Env.load_of_bytesAt {r off n : Nat} {bs : List UInt8} (hlen : bs.length = n)
    (h : BytesAt env.mem0 (env.base r + BitVec.ofNat 64 off) bs) :
    env.load r off n = BitVec.ofInt 64 (Int.ofBytes bs) := by
  unfold Env.load
  congr 2
  apply List.ext_getElem (by simp [hlen])
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [← addr_add, h i h2]
  rfl

omit [Labels] in
theorem findWrite_head {r o n i : Nat} {v : Sym} {ws : List Write} (hi : i < n) :
    findWrite r (o + i) (⟨r, o, n, v⟩ :: ws) = some (v, i) := by
  rw [findWrite_cons, ite_pos (show r = r ∧ o ≤ o + i ∧ o + i < o + n from
    ⟨rfl, by omega, by omega⟩), Nat.add_sub_cancel_left]

/-- **A write's bytes**: where `v`'s newest write covers the `n` bytes at `o` in region `r` (from
its byte 0), they are `v`'s low `n` bytes. -/
theorem Match.bytesAt_write (hm : Match env S m) {r o n : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hle : o + n ≤ sz) {v : Sym}
    (hw : ∀ i < n, findWrite r (o + i) S.mem = some (v, i)) :
    BytesAt m.dmem (b + BitVec.ofNat 64 o) ((List.range n).map (byteOf (v.eval env))) := by
  intro i hi
  rw [List.length_map, List.length_range] at hi
  rw [addr_add, hm.mem r b sz hb (o + i) (by omega)]
  unfold memByte
  rw [hw i hi]
  simp

omit [Labels] in
/-- The bytes `Int.toBytes` gives for a 64-bit value are its `byteOf`s. -/
theorem toBytes_byteOf (x : BitVec 64) :
    Int.toBytes 8 x.toInt = (List.range 8).map (byteOf x) := by
  apply List.ext_getElem? 
  intro i
  by_cases hi : i < 8
  · rw [show x.toInt = (x.setWidth (8 * 8)).toInt from by rw [BitVec.setWidth_eq],
      toBytes_setWidth x 8 i hi, List.getElem?_map, List.getElem?_range hi]
    rfl
  · rw [List.getElem?_eq_none (by rw [Int.toBytes_length]; omega),
      List.getElem?_eq_none (by simp; omega)]

omit [Labels] in
theorem mem_of_findWrite {r j : Nat} {ws : List Write} {v : Sym} {t : Nat}
    (h : findWrite r j ws = some (v, t)) : ∃ w ∈ ws, w.r = r ∧ w.off ≤ j ∧ j < w.off + w.n := by
  induction ws with
  | nil => cases h
  | cons w ws ih =>
    rw [findWrite_cons] at h
    by_cases hw : w.r = r ∧ w.off ≤ j ∧ j < w.off + w.n
    · exact ⟨w, List.mem_cons_self, hw⟩
    · rw [ite_neg hw] at h
      obtain ⟨w', hw', h'⟩ := ih h
      exact ⟨w', List.mem_cons_of_mem _ hw', h'⟩

/-- The addresses a write of `S` covers. -/
@[expose] def Written (env : Env) (S : SState) (a : BitVec 64) : Prop :=
  ∃ w ∈ S.mem, ∃ (b : BitVec 64) (sz : Nat), env.regions[w.r]? = some (b, sz) ∧
    b.toNat + w.off ≤ a.toNat ∧
    a.toNat < b.toNat + w.off + w.n

/-- **The bytes no write covers** are `env.mem0`'s. -/
theorem Match.get?_mem0 (hm : Match env S m) (hwf : env.WF) {a : BitVec 64}
    (ha : ¬Written env S a) : m.dmem.get? a = env.mem0.get? a := by
  by_cases hin : ∃ (r : Nat) (b : BitVec 64) (sz : Nat), env.regions[r]? = some (b, sz) ∧
      b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + sz
  · obtain ⟨r, b, sz, hb, h1, h2⟩ := hin
    have hnw := hwf.noWrap r b sz hb
    have hab : a = b + BitVec.ofNat 64 (a.toNat - b.toNat) := by
      apply BitVec.eq_of_toNat_eq
      rw [toNat_add_ofNat _ _ (by omega)]
      omega
    rw [hab, hm.mem r b sz hb _ (by omega)]
    unfold memByte
    cases hf : findWrite r (a.toNat - b.toNat) S.mem with
    | none => rfl
    | some vt =>
      obtain ⟨w, hw, hwr, hw1, hw2⟩ := mem_of_findWrite hf
      exact absurd ⟨w, hw, b, sz, hwr ▸ hb, by omega, by omega⟩ ha
  · exact hm.outside a fun r b sz hb hc => hin ⟨r, b, sz, hb, hc⟩

/-- Memory after a block without writes is `env.mem0`. -/
theorem Match.dmem_eq (hm : Match env S m) (hwf : env.WF) (h : S.mem = []) : m.dmem = env.mem0 :=
  Std.ExtHashMap.ext_getElem? fun a => by
    rw [← Std.ExtHashMap.get?_eq_getElem?, ← Std.ExtHashMap.get?_eq_getElem?]
    exact hm.get?_mem0 hwf fun ⟨w, hw, _⟩ => by rw [h] at hw; cases hw

/-- Memory after a block is `env.mem0` but where a write of the block covers it. -/
theorem Match.sameOutside (hm : Match env S m) (hwf : env.WF) :
    SameOutside env.mem0 m.dmem (Written env S) :=
  fun _ ha => hm.get?_mem0 hwf ha

omit [Labels] in
theorem Env.addr_in {env : Env} (hwf : env.WF) {r : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) {a : BitVec 64} (h1 : b.toNat ≤ a.toNat) :
    a = b + BitVec.ofNat 64 (a.toNat - b.toNat) := by
  have hnw := hwf.noWrap r b sz hb
  apply BitVec.eq_of_toNat_eq
  rw [toNat_add_ofNat _ _ (by omega)]
  omega

/-- **Mapped bytes stay mapped**: every byte of `env.mem0` is a byte of memory after a block. -/
theorem Match.kept (hm : Match env S m) (hwf : env.WF) : Kept env.mem0 m.dmem := by
  intro a ha
  by_cases hin : ∃ (r : Nat) (b : BitVec 64) (sz : Nat), env.regions[r]? = some (b, sz) ∧
      b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + sz
  · obtain ⟨r, b, sz, hb, h1, h2⟩ := hin
    have hab := Env.addr_in hwf hb h1
    rw [hab, hm.mem r b sz hb _ (by omega)]
    unfold memByte
    cases findWrite r (a.toNat - b.toNat) S.mem with
    | some vt => rfl
    | none => rw [← hab]; exact ha
  · rw [hm.outside a fun r b sz hb hc => hin ⟨r, b, sz, hb, hc⟩]
    exact ha

/-- The `n` bytes at `o` in region `r` after a block, as `bytesOf` reads them. -/
theorem Match.bytesOf (hm : Match env S m) (hwf : env.WF) {r o n : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hle : o + n ≤ sz) :
    NativeRustcArm.bytesOf m.dmem (b + BitVec.ofNat 64 o) n =
      (List.range n).map fun i => memByteD env S.mem r b (o + i) := by
  unfold NativeRustcArm.bytesOf
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [addr_add, hm.mem r b sz hb (o + i) (by omega), memByte_eq hwf hb (by omega)]
  rfl

omit [Labels] in
/-- **A byte of an environment load**: byte `t < n` of `env.load r off n` is the environment's byte
at `off + t` in region `r`. -/
theorem byteOf_load {r off n t : Nat} (ht : t < n) (hn : n ≤ 8) :
    byteOf (env.load r off n) t =
      (env.mem0.get? (env.base r + BitVec.ofNat 64 (off + t))).getD 0 := by
  unfold Env.load
  have hlt := natOfBytes_lt ((List.range n).map fun i =>
    (env.mem0.get? (env.base r + BitVec.ofNat 64 (off + i))).getD 0)
  simp only [List.length_map, List.length_range] at hlt
  have h64 : 2 ^ (8 * n) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  rw [ofBytes_natCast, BitVec.ofInt_natCast, byteOf_mod, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt h64), natOfBytes_div _ t (by simp; omega)]
  simp

omit [Labels] in
/-- An environment is well formed when each region is mapped and does not wrap, and the regions
are apart. -/
theorem Env.wf_of {env : Env}
    (h : AllOf (fun e : BitVec 64 × Nat => Mapped env.mem0 e.1 e.2 ∧ NoWrap e.1 e.2) env.regions)
    (hd : env.regions.Pairwise fun e e' => Apart e.1 e.2 e'.1 e'.2) : env.WF where
  noWrap r b n hb := (mem_of_allOf h (List.mem_of_getElem? hb)).2
  mapped r b n hb := (mem_of_allOf h (List.mem_of_getElem? hb)).1
  disjoint r r' b b' n n' hne hb hb' := by
    obtain ⟨hr, he⟩ := List.getElem?_eq_some_iff.mp hb
    obtain ⟨hr', he'⟩ := List.getElem?_eq_some_iff.mp hb'
    rw [List.pairwise_iff_getElem] at hd
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := hd r r' hr hr' hlt
      rw [he, he'] at this
      exact this
    · have := hd r' r hr' hr hlt
      rw [he, he'] at this
      exact this.symm

omit [Labels] in
/-- `InRange` of bytes that do not wrap is an interval of addresses. -/
theorem inRange_iff {x a : BitVec 64} {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64) :
    InRange x n a ↔ x.toNat ≤ a.toNat ∧ a.toNat < x.toNat + n := by
  unfold InRange
  rw [BitVec.toNat_sub]
  have := a.isLt
  have := x.isLt
  constructor
  · intro h
    by_cases hle : x.toNat ≤ a.toNat
    · rw [show 2 ^ 64 - x.toNat + a.toNat = (a.toNat - x.toNat) + 2 ^ 64 by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h
      omega
    · rw [Nat.mod_eq_of_lt (by omega)] at h
      omega
  · intro ⟨h1, h2⟩
    rw [show 2 ^ 64 - x.toNat + a.toNat = (a.toNat - x.toNat) + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-! ## Facts added mid-block

A block can be run in parts (`exec_then`), adding facts the proof knows to the state between them:
a register's value re-expressed (`Match.withReg`), an alias for a computed address
(`SState.withAlias`, e.g. a pointer loaded from memory, which a load or store through it then
places), a bound for an index (`SState.withBound`, which places an indexed access over the slots of
the bound). -/

/-- **A register's value re-expressed**: register `r` may be given any symbolic value `v` that is its
value, e.g. a byte offset as a bounded variable times a scale, or an address the proof knows. -/
theorem Match.withReg (hm : Match env S m) {r : XReg} {v : Sym}
    (h : (m.regs.getXReg r).toBitVec = v.eval env) : Match env (S.setReg r (some v)) m where
  regs r' u hu := by
    rcases S.reg_setReg r r' (some v) hu with ⟨rfl, hv⟩ | ⟨-, hv⟩
    · cases hv
      exact h
    · exact hm.regs r' u hv
  sp := hm.sp
  flags := hm.flags
  regions := hm.regions
  mem := hm.mem
  labels := hm.labels
  bounds := hm.bounds
  aliases := hm.aliases
  outside := hm.outside

/-- **An alias the machine state satisfies** may be added. -/
theorem Match.withAlias (hm : Match env S m) {x : Sym} {r : Nat} {o : Int}
    (h : x.eval env = env.base r + BitVec.ofInt 64 o) : Match env (S.withAlias x r o) m :=
  { hm with
    aliases := fun x' r' o' hl => by
      simp only [SState.withAlias, List.lookup_cons] at hl
      split at hl
      · rename_i hx
        rw [beq_iff_eq] at hx
        subst hx
        cases hl
        exact h
      · exact hm.aliases x' r' o' hl }

/-- **A bound the machine state satisfies** may be added. -/
theorem Match.withBound (hm : Match env S m) {x : Sym} {B : Nat} (h : (x.eval env).toNat < B) :
    Match env (S.withBound x B) m :=
  { hm with
    bounds := fun x' B' hb => by
      rcases List.mem_cons.mp hb with hb | hb
      · cases hb
        exact h
      · exact hm.bounds x' B' hb }

/-! ## Registers kept -/

/-- A register with the same symbolic value in two states of one environment has the same value. -/
theorem Match.reg_eq {S₀ : SState} {m₀ : MachineData} (hm₀ : Match env S₀ m₀) (hm : Match env S m)
    {r : XReg} {v : Sym} (h₀ : S₀.reg r = some v) (h : S.reg r = some v) :
    m.regs.getXReg r = m₀.regs.getXReg r :=
  UInt64.toBitVec_inj.mp ((hm.regs r v h).trans (hm₀.regs r v h₀).symm)

/-- SP with the same symbolic value in two states of one environment has the same value. -/
theorem Match.sp_eq {S₀ : SState} {m₀ : MachineData} (hm₀ : Match env S₀ m₀) (hm : Match env S m)
    (h : S.sp = S₀.sp) : m.regs.SP = m₀.regs.SP :=
  UInt64.toBitVec_inj.mp (hm.sp.trans (h ▸ hm₀.sp.symm))

/-- `S` keeps `S₀`'s SP and its known callee-saved registers. -/
@[expose] def keeps (S₀ S : SState) : Bool :=
  allXRegs.all (fun r => !calleeSaved r || ((S₀.reg r).isSome && S.reg r == S₀.reg r)) &&
    S.sp == S₀.sp

omit [Labels] in
theorem mem_allXRegs (r : XReg) : r ∈ allXRegs := by
  cases r <;> simp [allXRegs]

/-- **What a block keeps**: the callee-saved registers and SP, where the symbolic state keeps them
(`keeps`, checked by `decide` on the literal states), and the mapped bytes, from a state with the
environment's memory. -/
theorem Match.saved {S₀ : SState} {m₀ : MachineData} (hm₀ : Match env S₀ m₀) (hm : Match env S m)
    (hwf : env.WF) (hd : m₀.dmem = env.mem0) (h : keeps S₀ S = true) : Saved m₀ m := by
  simp only [keeps, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  refine ⟨fun r hr => ?_, Match.sp_eq hm₀ hm h.2, hd ▸ hm.kept hwf⟩
  have := h.1 r (mem_allXRegs r)
  simp only [hr, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq,
    Option.isSome_iff_exists] at this
  obtain ⟨⟨v, hv⟩, hS⟩ := this
  exact Match.reg_eq hm₀ hm hv (hS.trans hv)

omit [Labels] in
theorem _root_.NativeRustcArm.Saved.refl (m : MachineData) : Saved m m := ⟨fun _ _ => rfl, rfl, fun _ h => h⟩

omit [Labels] in
theorem _root_.NativeRustcArm.Saved.trans {m₀ m₁ m₂ : MachineData} (h₁ : Saved m₀ m₁) (h₂ : Saved m₁ m₂) :
    Saved m₀ m₂ :=
  ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), h₂.2.1.trans h₁.2.1,
    fun p hp => h₂.2.2 p (h₁.2.2 p hp)⟩

end

end NativeRustcArm.Sym
