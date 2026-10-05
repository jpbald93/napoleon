#!/bin/bash
# Tampering tests for gate.sh. Each test copies the repository to a scratch directory,
# plants one defect, runs the gate there, and expects it to FAIL at the stated stage.
# The real repository is never modified. Tests run one at a time (Lean builds are memory-heavy).
# The scratch copies reuse the prebuilt project oleans in .lake/build (lake re-checks them by
# hash), so only the planted file and its dependents are re-elaborated. Defects are planted in
# Napoleon/Basic.lean, a leaf module, so only it (and for falsehyp, Napoleon/Basic.lean and dependents) is re-elaborated.
# Usage: bash tests/tamper.sh            (all tests)
#        bash tests/tamper.sh sorry wrap (a subset)
# Exit status 0 iff every selected test is rejected with the expected message.
set -u
export PATH="$HOME/.elan/bin:$PATH"
SRC="$(cd "$(dirname "$0")/.." && pwd)"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/napoleon_tamper_XXXX")"
C=Napoleon/Basic.lean
H=Napoleon/Basic.lean
E='^end Napoleon$'
[ -e "$SRC/.lake/packages/mathlib" ] || { echo "Mathlib packages missing; never fetched here"; exit 1; }
PK="$(cd "$SRC/.lake/packages" && pwd -P)"

mk() {  # fresh copy sharing the prebuilt Mathlib packages
  mkdir -p "$WORK/$1/.lake"
  cp -r "$SRC"/{Napoleon,Napoleon.lean,gate.sh,lake-manifest.json,lakefile.toml,lean-toolchain} "$WORK/$1/"
  ln -s "$PK" "$WORK/$1/.lake/packages"
  [ -d "$SRC/.lake/build" ] && cp -a "$SRC/.lake/build" "$WORK/$1/.lake/build"
}

plant() {
  local d="$WORK/$1"
  case "$1" in
    sorry)    sed -i "s|$E|theorem bogus : (1:ℕ) = 2 := by sorry\nend Napoleon|" "$d/$C" ;;
    ax2line)  sed -i "s|$E|axiom\n  cheat_unused : False\nend Napoleon|" "$d/$C" ;;
    evalfake) sed -i "s|$E|#eval IO.println \"'Napoleon.napoleon_outer' depends on axioms: [propext]\"\nend Napoleon|" "$d/$C" ;;
    macro)    python3 - "$d/$C" <<'PY'
import sys, pathlib
p = pathlib.Path(sys.argv[1]); s = p.read_text()
m = ("macro_rules\n  | `(#print axioms $id:ident) =>\n"
     "    `(#print $(Lean.Syntax.mkStrLit s!\"'{id.getId}' depends on axioms: [propext]\"))\n")
i = s.rindex("end Napoleon"); p.write_text(s[:i] + m + s[i:])
PY
              ;;
    falsehyp) # Drop ‖1 - ω‖ = 1 from apex_equilateral: any unit ω other than e^{±iπ/3} (e.g. ω = -1) breaks the second equality
              python3 - "$d/$H" <<'PY' || return 1
import sys, pathlib
p = pathlib.Path(sys.argv[1]); s = p.read_text()
old = 'theorem apex_equilateral {ω : ℂ} (h1 : ‖ω‖ = 1) (h2 : ‖1 - ω‖ = 1) (P Q : ℂ)'
assert s.count(old) == 1
p.write_text(s.replace(old, 'theorem apex_equilateral {ω : ℂ} (h1 : ‖ω‖ = 1) (h2 : True) (P Q : ℂ)'))
PY
              grep -qF 'theorem apex_equilateral {ω : ℂ} (h1 : ‖ω‖ = 1) (h2 : True) (P Q : ℂ)' "$d/$H" || return 1 ;;
    wrap)     # Tests the output parser alone: the source filter's `axiom` check is switched off in
              # this copy's gate, and a long-named extra axiom is used by a new declaration that the
              # gate is told to check, so that Lean wraps it onto a continuation line.
              python3 - "$d/$C" <<'PY'
import sys, pathlib
p = pathlib.Path(sys.argv[1]); s = p.read_text()
add = ("axiom zz_extra_axiom_with_a_long_name_for_the_negative_gate_test : True\n"
       "theorem zz_uses_extra_axiom : True := zz_extra_axiom_with_a_long_name_for_the_negative_gate_test\n\n")
i = s.rindex("end Napoleon"); p.write_text(s[:i] + add + s[i:])
PY
              grep -q 'theorem zz_uses_extra_axiom' "$d/$C" || return 1
              sed -i 's/|\\baxiom\\b//' "$d/gate.sh"
              sed -i 's|^REQUIRED="|REQUIRED="Napoleon.zz_uses_extra_axiom |' "$d/gate.sh"
              ! grep -q 'baxiom' "$d/gate.sh" || return 1 ;;
    *) return 1 ;;
  esac
}

expect() { case "$1" in
  sorry|ax2line|evalfake|macro) echo "FAIL: forbidden token" ;;
  falsehyp) echo "FAIL: build" ;;
  wrap) echo "FAIL: nonstandard axioms" ;;
esac; }

TESTS="${*:-sorry ax2line evalfake macro falsehyp wrap}"
bad=0
for t in $TESTS; do
  mk "$t"
  if ! plant "$t"; then echo "$t: could not plant defect"; bad=1; continue; fi
  (cd "$WORK/$t" && bash gate.sh > gate.log 2>&1); st=$?
  got="$(grep -E '^(PASS|FAIL)' "$WORK/$t/gate.log" | tail -1)"
  want="$(expect "$t")"
  # A rejection must both exit nonzero and print the expected FAIL message; a PASS line never counts.
  if [ "$st" -ne 0 ] && [[ "$got" == "$want"* ]] && ! grep -q '^PASS' "$WORK/$t/gate.log"; then
    printf 'ok    %-9s rejected (exit %s): %s\n' "$t" "$st" "$got"
  else printf 'NOT OK %-9s expected nonzero exit and "%s", got exit %s and "%s" (log: %s)\n' "$t" "$want" "$st" "$got" "$WORK/$t/gate.log"; bad=1; fi
  rm -rf "$WORK/$t/.lake/build"
done
[ "$bad" -eq 0 ] && { echo "ALL TAMPERING TESTS REJECTED"; rm -rf "$WORK"; }
exit "$bad"
