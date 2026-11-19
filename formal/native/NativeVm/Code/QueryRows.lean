module

public import NativeVm.Code.Gadgets
public import NativeVm.Code.Data

/-!
# A query's rows as the phases hold them

`query` leaves the rows as one run of words (`Transcript.QueryRowsAt`, of the rows the statement
sees); the phases read them as `Code.RowsAt`, row `i` from word `width · i`. They agree when every
row has `width` words (`rowsAt_of_query`), which the model's `queryOpenings` guarantees: its rows
are as many as the positions, each as wide as the root's width (`queryOpenings_rows`).
-/

@[expose] public section

namespace NativeVm.Code

open Native NativeVm.Model NativeVm.Transcript LeanVM.Parameters LeanVM.Semantics
open LeanVM.Protocol LeanVM.Protocol.Compile

/-- Word `w · i + j` of a flattening of rows of `w` words is row `i`'s word `j`. -/
theorem getElem?_flatten_uniform {α : Type} {w : Nat} :
    ∀ (L : List (List α)), (∀ l ∈ L, l.length = w) → ∀ i j (hi : i < L.length), j < w →
      L.flatten[w * i + j]? = (L[i]'hi)[j]?
  | [], _, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | a :: L, hu, i, j, hi, hj => by
    have ha : a.length = w := hu a (List.mem_cons_self ..)
    rw [List.flatten_cons]
    cases i with
    | zero =>
      rw [Nat.mul_zero, Nat.zero_add, List.getElem?_append_left (by omega)]
      rfl
    | succ i =>
      rw [List.getElem?_append_right (by rw [ha, Nat.mul_succ]; omega), ha,
        show w * (i + 1) + j - w = w * i + j by rw [Nat.mul_succ]; omega]
      exact getElem?_flatten_uniform L (fun l hl ↦ hu l (List.mem_cons_of_mem _ hl)) i j
        (by simpa using hi) hj

/-- **`query`'s rows as `RowsAt`**, every row `width` words. -/
theorem rowsAt_of_query {mem : UInt64 → Option UInt64} {p : UInt64} {width : Nat}
    {rows : Array (Array UInt64)}
    (hq : QueryRowsAt mem p (rows.toList.map (·.toList.map K.ofLane)))
    (hw : ∀ i (h : i < rows.size), rows[i].size = width) (hcap : rows.size * width ≤ rowsWords) :
    RowsAt mem p width rows := by
  refine ⟨hcap, fun i hi ↦ ⟨hw i hi, fun j hj ↦ ?_⟩⟩
  have hu : ∀ l ∈ rows.toList.map (·.toList.map K.ofLane), l.length = width := fun l hl ↦ by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
    simpa using hw k (by simpa using hk)
  have hj' : j < width := hw i hi ▸ hj
  have hidx := getElem?_flatten_uniform _ hu i j (by simpa using hi) hj'
  simp only [List.getElem_map, Array.getElem_toList, List.getElem?_map, Array.getElem?_toList,
    Array.getElem?_eq_getElem hj, Option.map_some] at hidx
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hidx
  have := hq _ hlt
  rw [heq] at this
  show mem (wd p (width * i) + (8 * j).toUInt64) = _
  rw [wd_add, this]
  rfl

/-- A query that returned opened the next phase against root `i`. -/
theorem queryOpenings_some {t t' : TState} {i : Nat} {ps : Array UInt64}
    {rows : Array (Array UInt64)} (h : (Model.queryOpenings i ps).run t = some (rows, t')) :
    ∃ r ph, t.roots[i]? = some r ∧ t.openings[t.phase]? = some ph ∧
      Model.openPhase r.digest r.height r.width ps ph = some rows := by
  rw [Equiv.queryOpenings_run] at h
  split at h
  · rename_i r ph hr hp
    cases ho : Model.openPhase r.digest r.height r.width ps ph with
    | none => rw [ho] at h; cases h
    | some rows' =>
      rw [ho] at h
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨r, ph, hr, hp, ho⟩
  · cases h

/-- An opened phase's rows: its leaves, one per position, each `width` words. -/
theorem openPhase_some {root : Digest} {height width : Nat} {ps : Array UInt64}
    {ph : Array OpeningW} {rows : Array (Array UInt64)}
    (h : Model.openPhase root height width ps ph = some rows) :
    rows = ph.map (·.leaf) ∧ rows.size = ps.size ∧ ∀ j (hj : j < rows.size), rows[j].size = width := by
  unfold Model.openPhase at h
  split at h
  · rename_i hshape
    split at h
    · obtain rfl := Option.some.inj h
      rw [Bool.and_eq_true] at hshape
      obtain ⟨hall, hmap⟩ := hshape
      refine ⟨rfl, ?_, fun j hj ↦ ?_⟩
      · have := congrArg Array.size (beq_iff_eq.mp hmap)
        simpa using this
      · have := Array.all_eq_true.mp hall j (by simpa using hj)
        simp only [Bool.and_eq_true, beq_iff_eq] at this
        simpa using this.1
    · cases h
  · cases h

/-- **The model's rows**: as many as the positions, each as wide as root `i`. -/
theorem queryOpenings_rows {t t' : TState} {i : Nat} {ps : Array UInt64}
    {rows : Array (Array UInt64)} (h : (Model.queryOpenings i ps).run t = some (rows, t')) :
    ∃ r, t.roots[i]? = some r ∧ rows.size = ps.size ∧ ∀ j (hj : j < rows.size), rows[j].size = r.width := by
  obtain ⟨r, _, hr, _, ho⟩ := queryOpenings_some h
  obtain ⟨_, hs, hw⟩ := openPhase_some ho
  exact ⟨r, hr, hs, hw⟩

/-- **The rows are at most `wireMaxLeafWords` wide**: they are leaves of the decoded proof. -/
theorem queryOpenings_rows_le {env : Env} {t t' : TState} {s : QState} {i : Nat}
    {ps : Array UInt64} {rows : Array (Array UInt64)} (hc : CodeRel env t s)
    (h : (Model.queryOpenings i ps).run t = some (rows, t')) :
    ∀ j (hj : j < rows.size), rows[j].size ≤ wireMaxLeafWords := by
  intro j hj
  obtain ⟨r, ph, -, hp, ho⟩ := queryOpenings_some h
  obtain ⟨rfl, -, -⟩ := openPhase_some ho
  obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hp
  have hk : t.phase < env.proof.openings.length := by rw [← hc.openings_size]; exact hlt
  obtain ⟨_, width, _, hw, _, _, _, _, hd⟩ := hc.decoded.2.2.2.2.2 t.phase hk
  have e : env.proof.openings[t.phase] = Equiv.phaseOpenings t.openings[t.phase] := by
    simp only [← hc.openings, List.getElem_map, Array.getElem_toList]
  have hj' : j < env.proof.openings[t.phase].length := by
    rw [e]; simpa [Equiv.phaseOpenings] using hj
  have hl := (hd j hj').1
  simp only [e, Equiv.phaseOpenings, List.getElem_map, Array.getElem_toList,
    OpeningW.toOpening, List.length_map, Array.length_toList] at hl
  simp only [Array.getElem_map]
  omega

end NativeVm.Code
