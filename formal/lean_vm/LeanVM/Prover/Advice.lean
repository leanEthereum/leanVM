/-
  LeanVM.Prover.Advice

  The text form of a run's advice (`Program::advice_text`), parsed.
-/

module

public import Statement.Prover.Execute

/-!
# The advice's text

`parseAdvice` reads the advice the Rust writes (`Program::advice_text`, `crates/leanvm_core/src/cpu/hints.rs`):
whitespace-separated tokens, `leanvm-advice 1`, `main_frame n`, `hints` and per pc its hints (a tag and
its fields, a field element as two hexadecimal limbs), `streams` and per stream its entries. The guest's
own (`LeanVM/Guest/Data/Advice.lean`) has no stream. Nothing is proved about it: the executor trusts no
advice.
-/

@[expose] public section

namespace LeanVM.Prover.AdviceText

open LeanVM.Parameters LeanVM.Prover.Exec

/-- A hexadecimal digit's value. -/
def hexDigitOf? (c : Char) : Option ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- A parser over the advice's whitespace-separated tokens. -/
abbrev P := StateT ℕ (ReaderT (Array String) (Except String))

def tok : P String := do
  let i ← get
  let some t := (← read)[i]? | throw "advice: unexpected end"
  set (i + 1)
  pure t

def expect (t : String) : P Unit := do
  let u ← tok
  unless u = t do throw s!"advice: expected `{t}`, found `{u}`"

def nat : P ℕ := do
  let t ← tok
  let some n := t.toNat? | throw s!"advice: not a number: `{t}`"
  pure n

def hex : P ℕ := do
  let t ← tok
  t.toList.foldlM (fun n c ↦ match hexDigitOf? c with
    | some d => pure (16 * n + d)
    | none => throw s!"advice: not hexadecimal: `{t}`") 0

def word : P E := do
  let c0 ← hex
  let c1 ← hex
  pure (E.ofLimbs (K.ofBits c0) (K.ofBits c1))

def dest : P BitsDest := do
  match ← tok with
  | "s" => .stack <$> nat
  | "h" => .heap <$> nat
  | t => throw s!"advice: not a destination: `{t}`"

def many {α : Type} (n : ℕ) (p : P α) : P (List α) := (List.range n).mapM fun _ ↦ p

def hint : P Hint := do
  match ← tok with
  | "fa" => .frameAddress <$> nat
  | "af" => return .allocFrames (← nat) (← nat) (← nat) (K.ofBits (← hex)) (← nat)
  | "al" => return .alloc (← nat) (← nat)
  | "ad" => return .allocDyn (← nat) (← nat)
  | "av" => return .allocAdvice (← nat) (← tok)
  | "aa" => do
    let ptr ← nat
    let sel ← nat
    let n ← nat
    return .allocArm ptr sel (← many n nat)
  | "ca" => return .cellAddress (← nat) (← nat)
  | "ws" => return .witnessStack (← tok) (← nat) (← nat)
  | "wh" => return .witnessHeap (← tok) (← nat) (← nat) (← nat)
  | "lc" => return .log2Ceil (← dest) (← nat) (← nat) (← nat)
  | "bd" => return .bitDecompose (← nat) (← dest) (← nat)
  | "be" => return .bitDecomposeExp (← nat) (← dest) (← nat)
  | "dd" =>
    return .digitDecomposeExp (← nat) (← dest) (← nat) (← nat) (← nat) (← nat)
      (match ← tok with | "-" => none | t => t.toNat?)
  | "we" => return .windowsExp (← nat) (← dest) (← nat) (← nat) (← nat) (← nat)
  | "fl" => return .fieldLimbs (← nat) (← nat) (← nat)
  | "iv" => return .inverse (← nat) (← nat)
  | t => throw s!"advice: not a hint: `{t}`"

def advice : P Advice := do
  expect "leanvm-advice"; expect "1"; expect "main_frame"
  let mainFrame ← nat
  expect "hints"
  let hints ← many (← nat) do
    let pc ← nat
    return (pc, ← many (← nat) hint)
  expect "streams"
  let streams ← many (← nat) do
    let name ← tok
    return (name, ← many (← nat) do many (← nat) word)
  pure ⟨mainFrame, hints, streams⟩

/-- The advice a text holds. -/
def _root_.LeanVM.Prover.parseAdvice (text : String) : Except String Advice :=
  (advice.run' 0).run ((text.splitToList Char.isWhitespace).filter (· ≠ "")).toArray

end LeanVM.Prover.AdviceText
