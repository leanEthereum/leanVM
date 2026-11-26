#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
export ELAN_TOOLCHAIN=$(cat "$here/../lean-toolchain")
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cd "$work"
export LEAN_PATH=$work

cat > AxiomControlSource.lean <<'LEAN'
module
public import Lean

private axiom injected : True
public theorem importedCustom : True := injected
LEAN

cat > AxiomControlTargets.lean <<'LEAN'
module
public import Lean
import AxiomControlSource

public theorem noAxioms : True := True.intro
public theorem onlyPropext : (True ∧ True) = True :=
  propext ⟨fun _ => True.intro, fun h => ⟨h, h⟩⟩
public noncomputable def onlyChoice : Nat := Classical.choice ⟨0⟩
public theorem onlyQuot :
    Quot.mk (fun (_ _ : Nat) => True) 0 = Quot.mk (fun (_ _ : Nat) => True) 1 :=
  Quot.sound True.intro
public theorem usesCustom : True := importedCustom
public theorem usesSorry : False := by sorry
public theorem usesNative : (1 : Nat) + 1 = 2 := by native_decide
LEAN

cat > AxiomControlChanged.lean <<'LEAN'
prelude
axiom propext : Prop
LEAN

for module in AxiomControlSource AxiomControlTargets AxiomControlChanged; do
  lean -o "$module.olean" "$module.lean"
done

expect_status() {
  local expected=$1 actual=0
  shift
  bash "$here/axiom-footprint.sh" control "$@" > check.out 2>&1 || actual=$?
  if [ "$actual" != "$expected" ]; then
    cat check.out
    printf 'Expected exit %s, got %s\n' "$expected" "$actual" >&2
    exit 1
  fi
}

expect_status 0 'AxiomControlTargets AxiomControlSource' noAxioms onlyPropext onlyChoice onlyQuot
grep -Fx "'noAxioms' does not depend on any axioms" check.out
grep -Fx "'onlyPropext' depends on axioms: [propext]" check.out
grep -Fx "'onlyChoice' depends on axioms: [Classical.choice]" check.out
grep -Fx "'onlyQuot' depends on axioms: [Quot.sound]" check.out

expect_status 1 AxiomControlTargets usesCustom usesSorry usesNative missingDeclaration
grep -E "usesCustom depends on more axioms: .*injected" check.out
grep -F "usesSorry depends on more axioms: 'sorryAx'" check.out
grep -E "usesNative depends on more axioms: .*native" check.out
grep -F "unknown declaration 'missingDeclaration'" check.out

expect_status 1 AxiomControlChanged propext
grep -F "uses a changed standard axiom 'propext'" check.out

expect_status 2 AxiomControlTargets
grep -F 'usage: axiom-footprint.sh' check.out
