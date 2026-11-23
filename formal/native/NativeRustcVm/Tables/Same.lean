module

public import NativeRustcVm.Layout.RepLemmas
public import NativeRustcVm.Tables.Rep
public import NativeRustcVm.Transcript.Frame

/-!
# Representations over bytes that stayed the same

A representation the phases read holds in a memory whose bytes over it are the same
(`NativeRustcVm.Layout.Same`): the words (`WordsAt.of_same`), the layout (`LayoutWAt.of_same`).
-/

namespace NativeRustcVm.Tables

open NativeVm.Model NativeRustcVm.Layout
open NativeRustcVm.Transcript (off length_flatMap_wordBytes)

public section

variable {d d' : Mem 64} {a : BitVec 64}

theorem WordsAt.of_same {ws : List UInt64} {n : Nat} (h : WordsAt d a ws) (hs : Same d d' a n)
    (hl : 8 * ws.length ≤ n) : WordsAt d' a ws :=
  BytesAt.of_same h hs (by rw [length_flatMap_wordBytes]; exact hl)

theorem PlacementWAt.of_same {p : Option LeanVM.Protocol.Verifier.Placement}
    (h : PlacementWAt d a p) (hs : Same d d' a 24) : PlacementWAt d' a p := by
  cases p with
  | none => exact WordAt.of_same h hs (by omega)
  | some p =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    exact ⟨WordAt.of_same h1 hs (by omega), h2, h3,
      WordAt.of_same h4 (hs.sub (o := 8) (k := 8) (by omega)) le_rfl,
      WordAt.of_same h5 (hs.sub (o := 16) (k := 8) (by omega)) le_rfl⟩

/-- **The layout** over bytes that stayed the same. -/
theorem LayoutWAt.of_same {L : LayoutW} (h : LayoutWAt d a L) (hs : Same d d' a layoutBytes) :
    LayoutWAt d' a L := by
  have hb : layoutBytes = 3912 := rfl
  have hp : placementBytes = 24 := rfl
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ⟨rows, hr1, hr2, hr3, hr4⟩, h10, h11⟩ := h
  refine ⟨h1, WordAt.of_same h2 hs (by omega), h3,
    WordAt.of_same h4 (hs.sub (o := 8) (k := 8) (by omega)) le_rfl, h5,
    WordAt.of_same h6 (hs.sub (o := 16) (k := 8) (by omega)) le_rfl, h7, h8,
    WordsAt.of_same h9 (hs.sub (o := 24) (k := 48) (by omega)) (by simp [h7, nTables]),
    ⟨rows, hr1, hr2, WordsAt.of_same hr3 (hs.sub (o := 72) (k := 48) (by omega))
      (by simp [hr1, nTables]), hr4⟩, h10, fun c hc ↦ ?_⟩
  have hc' : c < 158 := by rw [h10] at hc; exact hc
  exact PlacementWAt.of_same (h11 c hc) (hs.sub (o := 120 + placementBytes * c) (k := 24)
    (by rw [hp]; omega))

/-- **The claims** over bytes that stayed the same. -/
theorem ClaimsWAt.of_same {cs : Array ColumnClaimW} (h : ClaimsWAt d a cs)
    (hs : Same d d' a claimsBytes) : ClaimsWAt d' a cs := by
  have hb : claimsBytes = 8 + columnClaimBytes * claimCap := rfl
  refine ⟨h.len_le, WordAt.of_same h.len hs (by rw [hb]; omega), fun i hi ↦ ?_⟩
  have hc := h.len_le
  have hk : 8 + columnClaimBytes * i + columnClaimBytes ≤ claimsBytes := by
    have h1 := Nat.mul_le_mul_left columnClaimBytes (show i + 1 ≤ claimCap by omega)
    rw [Nat.mul_succ] at h1
    rw [hb]
    omega
  exact (h.claims i hi).of_same (hs.sub hk)

theorem EWsAt.of_same {xs : List EW} {n : Nat} (h : EWsAt d a xs) (hs : Same d d' a n)
    (hl : 16 * xs.length ≤ n) : EWsAt d' a xs :=
  BytesAt.of_same h hs (by rw [length_ewsBytes]; exact hl)

/-- A term over bytes that stayed the same. -/
theorem TermWAt.of_same {t : TermW} (h : TermWAt d a t) (hs : Same d d' a termBytes) :
    TermWAt d' a t where
  degree_le := h.degree_le
  degree := WordAt.of_same h.degree hs (by decide)
  cols_lt := h.cols_lt
  cols i hi := WordAt.of_same (h.cols i hi) (hs.sub (o := 8 + 8 * i) (k := 8)
    (by have := h.degree_le; unfold termBytes; omega)) (Nat.le_refl _)
  coeff := EWAt.of_same h.coeff (hs.sub (o := 24) (k := 16) (by decide)) (Nat.le_refl _)

/-- A form over bytes that stayed the same. -/
theorem FormBufAt.of_same {f : FormW} (h : FormBufAt d a f) (hs : Same d d' a formBufBytes) :
    FormBufAt d' a f := by
  have hle := h.len_le
  unfold formCap at hle
  refine ⟨h.len_le, WordAt.of_same h.len hs (by decide), fun i hi ↦ ?_⟩
  have ht := h.terms i hi
  have e : off (off a 8) (termBytes * i) = off a (8 + termBytes * i) := by
    simp only [off]; rw [addr_add_add]
  rw [e] at ht ⊢
  exact TermWAt.of_same ht (hs.sub (by unfold termBytes formBufBytes formCap termBytes; omega))

/-- **The bus's result** over bytes that stayed the same. -/
theorem BusWAt.of_same {r : BusResultW} (h : NativeRustcVm.Bus.BusWAt d a r)
    (hs : Same d d' a NativeRustcVm.Bus.busBytes) : NativeRustcVm.Bus.BusWAt d' a r := by
  have hb : NativeRustcVm.Bus.busBytes = 107768 := rfl
  have hf : formBufBytes = 5928 := rfl
  refine ⟨h.forms_size, h.row_size, fun t ht s hs' ↦ ?_, ?_, h.totals_size, ?_⟩
  · have h1 := h.row_size t ht
    have h2 := h.forms_size
    exact FormBufAt.of_same (h.forms t ht s hs') (hs.sub (by rw [hb, hf]; unfold nTables at h2; omega))
  · obtain ⟨hle, hw, he⟩ := h.point
    have hl : r.point.toList.length ≤ 63 := hle
    refine ⟨hle, WordAt.of_same hw (hs.sub (o := 106704) (k := 8) (by rw [hb]; omega)) le_rfl,
      EWsAt.of_same he ?_ (Nat.le_refl _)⟩
    · have := hs.sub (o := 106704 + 8) (k := 16 * r.point.toList.length) (by rw [hb]; omega)
      simp only [off] at this ⊢
      rwa [← addr_add_add] at this
  · have hl : r.totals.toList.length = 3 := by simp [h.totals_size]
    exact EWsAt.of_same h.totals (hs.sub (o := 107720) (k := 48) (by rw [hb])) (by omega)

/-- **The tables' points and evaluations** over bytes that stayed the same. -/
theorem TableEvalsAt.of_same {ev : Array (Array EW × Array EW)} (h : TableEvalsAt d a ev)
    (hs : Same d d' a tableEvalsBytes) : TableEvalsAt d' a ev := by
  refine ⟨h.1, fun i hi ↦ ?_⟩
  have hi6 : i < 6 := by have := h.1; unfold nTables at this; omega
  have hsi : Same d d' (a + BitVec.ofNat 64 (tableEvalBytes * i)) tableEvalBytes :=
    hs.sub (by unfold tableEvalsBytes nTables tableEvalBytes; omega)
  obtain ⟨hp, hv⟩ := h.2 i hi
  exact ⟨BufEWAt.of_same hp hsi (by decide),
    BufEWAt.of_same hv (hsi.sub (o := valuesOff) (k := 1480) (by decide)) (by decide)⟩

end

end NativeRustcVm.Tables
