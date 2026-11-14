/-
  LeanVM.Guest.EndExecYCur

  The executor's stream cursor: what each hint and instruction does to it, and the guest's streams
  by name.
-/

module

public import LeanVM.Prover.ExecuteHint
public import LeanVM.Guest.Executor

/-!
# The stream cursor

`popsOn S h`: hint `h` pops an entry of stream `S` (a witness hint on `S`, an `allocAdvice` on `S`).
`hints_cursor`: the hints at a pc move each stream's cursor by the entries they pop of it;
`runOp_cursor`: an instruction keeps the cursor. `streams_guest`: on the guest's advice, the
executor's stream `S` is the honest pushes on `S`, in order, wherever there is one.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Prover.Exec

@[expose] public section

/-- **Hint `h` pops an entry of stream `S`.** -/
def popsOn (S : String) : Hint → Bool
  | .witnessStack n .. | .witnessHeap n .. | .allocAdvice _ n => n == S
  | _ => false

/-! ## The primitives keep the cursor -/

theorem cur_withMem {s s' : St} {f : Mem → Except Fault Mem} (h : s.withMem f = .ok s') :
    s'.cursor = s.cursor := by
  obtain ⟨m, -, rfl⟩ := St.withMem_ok h
  rfl

theorem cur_logOr {s s' : St} {x : K} {b k : ℕ} {f : Fault} (h : s.logOr x b f = .ok (k, s')) :
    s'.cursor = s.cursor := by
  unfold St.logOr at h
  rw [St.log_eq] at h
  split at h
  · rename_i k' s1 hp
    simp only [pure_ok, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp only [Prod.mk.injEq] at hp
    obtain ⟨-, rfl⟩ := hp
    rfl
  · simp at h

theorem cur_allocate {s s' : St} {ptr size : ℕ} (h : allocate s ptr size = .ok s') :
    s'.cursor = s.cursor := by
  unfold allocate at h
  dsimp only at h
  split_ifs at h
  · simp only [pure_ok] at h; subst h; rfl
  · rw [bind_ok] at h
    obtain ⟨next, -, h⟩ := h
    rw [bind_ok] at h
    obtain ⟨s1, h1, h⟩ := h
    simp only [pure_ok] at h
    subst h
    have := cur_withMem h1
    exact this

theorem cur_heapBase {s s' : St} {c b : ℕ} {what : String} (h : heapBase s c what = .ok (b, s')) :
    s'.cursor = s.cursor := by
  unfold heapBase at h
  rw [bind_ok] at h
  obtain ⟨p, -, h⟩ := h
  exact cur_logOr h

theorem cur_bitsBase {s s' : St} {d : BitsDest} {what : String} {b : ℕ}
    (h : bitsBase s d what = .ok (b, s')) : s'.cursor = s.cursor := by
  unfold bitsBase at h
  split at h
  · simp only [pure_ok, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  · exact cur_heapBase h

theorem cur_pop {C : Ctx} {s s' : St} {name : String} {len : ℕ} {v : List E}
    (h : pop C s name len = .ok (v, s')) :
    s'.cursor = s.cursor.insert name (s.cursor.getD name 0 + 1) := by
  unfold pop at h
  split at h
  · dsimp only at h
    split at h
    · split_ifs at h
      · cases h
      · simp only [pure_ok, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        rfl
    · simp at h
  · simp at h

theorem cur_popEntry {C : Ctx} {s s' : St} {name : String} {v : List E}
    (h : popEntry C s name = .ok (v, s')) :
    s'.cursor = s.cursor.insert name (s.cursor.getD name 0 + 1) := by
  unfold popEntry at h
  split at h
  · dsimp only at h
    split at h
    · simp only [pure_ok, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rfl
    · simp at h
  · simp at h

theorem getD_insert_succ (c : Std.HashMap String ℕ) (name S : String) :
    (c.insert name (c.getD name 0 + 1)).getD S 0 = c.getD S 0 + if name == S then 1 else 0 := by
  rw [Std.HashMap.getD_insert]
  split_ifs with h
  · rw [beq_iff_eq] at h; subst h; rfl
  · rfl

/-! ## A hint, an instruction -/

/-- **A hint moves stream `S`'s cursor by the entry it pops of it.** -/
theorem runHint_cursor {C : Ctx} {s s' : St} {hint : Hint} (h : runHint C s hint = .ok s') (S : String) :
    s'.cursor.getD S 0 = s.cursor.getD S 0 + if popsOn S hint then 1 else 0 := by
  have keep : s'.cursor = s.cursor → s'.cursor.getD S 0 = s.cursor.getD S 0 + 0 := fun e ↦ by rw [e]; rfl
  cases hint with
  | frameAddress offset =>
    simp only [runHint, bind_ok, pure_ok] at h
    obtain ⟨c, -, rfl⟩ := h
    rfl
  | alloc ptr size => exact keep (cur_allocate h)
  | allocDyn ptr size =>
    simp only [runHint, bind_ok] at h
    obtain ⟨sz, -, ⟨n, s1⟩, h1, h⟩ := h
    exact keep ((cur_allocate h).trans (cur_logOr h1))
  | allocAdvice ptr stream =>
    simp only [runHint, bind_ok] at h
    obtain ⟨⟨v, s1⟩, h1, h⟩ := h
    have e1 := cur_popEntry h1
    have hs1 : s'.cursor = s1.cursor := by
      rcases v with _ | ⟨w, _ | ⟨w', v⟩⟩ <;> dsimp only at h
      · simp only [pure_ok] at h
        subst h
        rfl
      · simp only [bind_ok] at h
        obtain ⟨sz, -, ⟨n, s2⟩, h2, h⟩ := h
        exact (cur_allocate h).trans (cur_logOr h2)
      · simp at h
    rw [hs1, e1, getD_insert_succ]
    rfl
  | allocArm ptr sel sizes =>
    simp only [runHint, bind_ok] at h
    obtain ⟨x, -, ⟨k, s1⟩, h1, h⟩ := h
    split at h
    · exact keep ((cur_allocate h).trans (cur_logOr h1))
    · simp at h
  | cellAddress ptr cell =>
    simp only [runHint, bind_ok] at h
    obtain ⟨c, -, h⟩ := h
    exact keep (cur_withMem h)
  | allocFrames ptr size stop startInverse tail =>
    simp only [runHint, bind_ok] at h
    obtain ⟨sp, -, h⟩ := h
    split_ifs at h
    · simp [bind_ok] at h
    · rw [bind_ok] at h
      obtain ⟨⟨n, s1⟩, h1, h⟩ := h
      exact keep ((cur_allocate h).trans (cur_logOr h1))
  | witnessStack name base len =>
    simp only [runHint, bind_ok] at h
    obtain ⟨⟨v, s1⟩, h1, h⟩ := h
    rw [cur_withMem h, cur_pop h1, getD_insert_succ]
    rfl
  | witnessHeap name ptr lo len =>
    simp only [runHint, bind_ok] at h
    obtain ⟨⟨b, s1⟩, h1, ⟨v, s2⟩, h2, h⟩ := h
    rw [cur_withMem h, cur_pop h2, cur_heapBase h1, getD_insert_succ]
    rfl
  | log2Ceil bits dst nbits floor =>
    simp only [runHint, bind_ok] at h
    obtain ⟨⟨b, s1⟩, h1, h⟩ := h
    exact keep ((cur_withMem h).trans (cur_bitsBase h1))
  | bitDecompose value bits nbits =>
    simp only [runHint, bind_ok] at h
    obtain ⟨⟨b, s1⟩, h1, h⟩ := h
    exact keep ((cur_withMem h).trans (cur_bitsBase h1))
  | bitDecomposeExp value bits nbits =>
    simp only [runHint, bind_ok] at h
    obtain ⟨n, -, ⟨b, s1⟩, h1, h⟩ := h
    exact keep ((cur_withMem h).trans (cur_bitsBase h1))
  | windowsExp value dest pos start width count =>
    simp only [runHint, bind_ok] at h
    obtain ⟨⟨b, s1⟩, h1, h⟩ := h
    exact keep ((cur_withMem h).trans (cur_bitsBase h1))
  | digitDecomposeExp value dst nbits ndigits digitBits start startCell =>
    simp only [runHint, bind_ok] at h
    obtain ⟨n, -, h⟩ := h
    split at h
    all_goals
      simp only [bind_ok] at h
      obtain ⟨st, -, ⟨b, s1⟩, h1, h⟩ := h
      exact keep ((cur_withMem h).trans (cur_bitsBase h1))
  | fieldLimbs value base len => exact keep (cur_withMem h)
  | inverse value dst =>
    simp only [runHint] at h
    exact keep (cur_withMem h)

/-- **The hints at a pc move stream `S`'s cursor by the entries they pop of it.** -/
theorem hints_cursor {C : Ctx} (S : String) :
    ∀ (l : List Hint) (s s' : St), l.foldlM (runHint C) s = .ok s' →
      s'.cursor.getD S 0 = s.cursor.getD S 0 + (l.filter (popsOn S)).length
  | [], s, s', h => by
    simp only [List.foldlM_nil, pure_ok] at h; subst h; rfl
  | x :: l, s, s', h => by
    rw [List.foldlM_cons, bind_ok] at h
    obtain ⟨s1, h1, h⟩ := h
    rw [hints_cursor S l s1 s' h, runHint_cursor h1 S, List.filter_cons]
    by_cases hp : popsOn S x = true
    · rw [ite_eq_left hp, ite_eq_left hp, List.length_cons]; omega
    · rw [ite_eq_right hp, ite_eq_right hp]; omega

/-- **An instruction keeps the cursor.** -/
theorem runOp_cursor {C : Ctx} {s s' : St} {op : Op} (e : runOp C s op = .ok s') : s'.cursor = s.cursor := by
  cases op with
  | xor a b c =>
    simp only [runOp, bind_ok, pure_ok] at e
    obtain ⟨_, -, _, -, _, -, _, -, _, -, s1, h1, rfl⟩ := e
    have := cur_withMem h1
    exact this
  | mul a b c =>
    simp only [runOp, bind_ok, pure_ok] at e
    obtain ⟨_, -, _, -, _, -, s1, h1, rfl⟩ := e
    have := cur_withMem h1
    exact this
  | set o k =>
    simp only [runOp, bind_ok, pure_ok] at e
    obtain ⟨_, -, s1, h1, rfl⟩ := e
    have := cur_withMem h1
    exact this
  | deref o1 o2 o3 mode =>
    simp only [runOp, bind_ok] at e
    obtain ⟨_, -, p, -, e⟩ := e
    split_ifs at e
    · exact absurd e (by intro h; cases h)
    obtain ⟨⟨a2, s1⟩, h1, e⟩ := bind_ok.mp e
    simp only [bind_ok, pure_ok] at e
    obtain ⟨_, -, s2, h2, rfl⟩ := e
    have := cur_withMem h2
    obtain ⟨D, rfl⟩ := St.derefCell_dl h1
    exact this
  | jump c d f =>
    simp only [runOp, bind_ok] at e
    obtain ⟨_, -, _, -, _, -, _, -, vc, -, _, -, vd, -, _, -, vf, -, s1, h1, e⟩ := e
    split_ifs at e
    · simp only [pure_ok] at e; subst e; have := cur_withMem h1; exact this
    · rw [bind_ok] at e
      obtain ⟨⟨pc, s2⟩, h2, e⟩ := e
      rw [bind_ok] at e
      obtain ⟨⟨fp, s3⟩, h3, e⟩ := e
      simp only [pure_ok] at e
      subst e
      exact (cur_logOr h3).trans ((cur_logOr h2).trans (cur_withMem h1))
  | keccak ins out inOdd outOdd count =>
    simp only [runOp, bind_ok, pure_ok] at e
    obtain ⟨_, -, _, -, _, -, s1, h1, rfl⟩ := e
    have := cur_withMem h1
    exact this

/-! ## The guest's streams -/

theorem names_spec : ∀ (ps : List (String × List E)) (ns : List String), ns.Nodup →
    (ps.foldl (fun ns p ↦ if ns.contains p.1 then ns else ns ++ [p.1]) ns).Nodup ∧
      ∀ S, S ∈ ps.foldl (fun ns p ↦ if ns.contains p.1 then ns else ns ++ [p.1]) ns ↔ S ∈ ns ∨ ∃ p ∈ ps, p.1 = S
  | [], ns, h => ⟨h, fun S ↦ by simp⟩
  | p :: ps, ns, h => by
    rw [List.foldl_cons]
    split_ifs with hc
    · obtain ⟨h1, h2⟩ := names_spec ps ns h
      refine ⟨h1, fun S ↦ ?_⟩
      rw [h2]
      have hc' : p.1 ∈ ns := by simpa using hc
      constructor
      · rintro (h | ⟨q, hq, rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, rfl⟩
      · rintro (h | ⟨q, hq, rfl⟩)
        · exact Or.inl h
        · rcases List.mem_cons.mp hq with rfl | hq
          · exact Or.inl hc'
          · exact Or.inr ⟨q, hq, rfl⟩
    · have hn : (ns ++ [p.1]).Nodup :=
        List.nodup_append.mpr ⟨h, List.nodup_singleton _, fun a ha b hb ↦ by
          rw [List.mem_singleton] at hb; subst hb; rintro rfl; exact hc (by simpa using ha)⟩
      obtain ⟨h1, h2⟩ := names_spec ps (ns ++ [p.1]) hn
      refine ⟨h1, fun S ↦ ?_⟩
      rw [h2, List.mem_append, List.mem_singleton]
      constructor
      · rintro ((h | rfl) | ⟨q, hq, rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨p, List.mem_cons_self, rfl⟩
        · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, rfl⟩
      · rintro (h | ⟨q, hq, rfl⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hq with rfl | hq
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr ⟨q, hq, rfl⟩

/-- **A stream of grouped pushes**: on a stream some push is on, the pushes on it, in order. -/
theorem streams_group {adv : Advice} {C : Ctx} {prog : LeanIsaProgram} (hC : Ctx.of prog adv = .ok C)
    {ps : List (String × List E)} (hs : adv.streams = Hints.group ps) {S : String} (hS : ∃ p ∈ ps, p.1 = S) :
    C.streams[S]? = some ((ps.filter (·.1 == S)).map (·.2)).toArray := by
  simp only [Ctx.of, bind_ok, pure_ok] at hC
  obtain ⟨ops, -, rfl⟩ := hC
  rw [hs, Hints.group]
  obtain ⟨hnd, hmem⟩ := names_spec ps [] List.nodup_nil
  generalize ps.foldl (fun ns p ↦ if ns.contains p.1 then ns else ns ++ [p.1]) [] = ns at hnd hmem
  refine Std.HashMap.getElem?_ofList_of_mem (k := S) (beq_self_eq_true S) ?_ ?_
  · rw [List.map_map, List.pairwise_map]
    refine hnd.imp fun {a b} hab ↦ ?_
    simpa using hab
  · rw [List.map_map, List.mem_map]
    exact ⟨S, (hmem S).mpr (Or.inr hS), rfl⟩

/-- **The guest's streams**: stream `S`, wherever some honest push is on it, is the honest pushes on
`S`, in order. -/
theorem streams_guest {seed s w} {C : Ctx}
    (hC : Ctx.of guestProgram (guestAdvice seed s w) = .ok C) {S : String}
    (hS : ∃ p ∈ Hints.honestPushes bytecodeShape seed s w, p.1 = S) :
    C.streams[S]? = some (((Hints.honestPushes bytecodeShape seed s w).filter (·.1 == S)).map (·.2)).toArray :=
  streams_group hC rfl hS

end

end LeanVM.Guest.EndExec
