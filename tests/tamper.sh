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
WORK="$(mktemp -d "${TMPDIR:-/tmp}/napoleon_tamper_XXXXXX")"
C=Napoleon/Basic.lean
H=Napoleon/Basic.lean
EL='end Napoleon'   # the namespace's closing line (defects are planted just before it)

# Portable text helpers (POSIX awk only: no in-place sed, no Python). Strings are passed through
# the environment, not `awk -v`, so backslashes in them are taken literally. Both fail (return 1,
# file untouched) if the marker / old text is not found.
# ins_before_last FILE TEXT MARK: insert TEXT (may contain real newlines) before the last line equal to MARK.
ins_before_last() { _T="$2" _M="$3" awk '{ L[NR]=$0; if ($0==ENVIRON["_M"]) last=NR } END { if (!last) exit 1; for(i=1;i<=NR;i++){ if(i==last) printf "%s\n", ENVIRON["_T"]; print L[i] } }' "$1" > "$1.$$.tmp" && mv "$1.$$.tmp" "$1" || { rm -f "$1.$$.tmp"; return 1; }; }
# subst_lit FILE OLD NEW [AFTER]: replace the first literal occurrence of OLD by NEW; with AFTER, only
# on the first line containing AFTER or the three lines following it.
subst_lit()      { _O="$2" _N="$3" _A="${4-}" awk '{ A=ENVIRON["_A"]; if(A!="" && !st && index($0,A)>0){ st=1; left=4 } if(!done && (A=="" || left>0)){ p=index($0,ENVIRON["_O"]); if(p>0){ $0=substr($0,1,p-1) ENVIRON["_N"] substr($0,p+length(ENVIRON["_O"])); done=1 } } if(left>0) left--; print } END { if(!done) exit 1 }' "$1" > "$1.$$.tmp" && mv "$1.$$.tmp" "$1" || { rm -f "$1.$$.tmp"; return 1; }; }
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
    sorry)    ins_before_last "$d/$C" 'theorem bogus : (1:ℕ) = 2 := by sorry' "$EL" ;;
    ax2line)  ins_before_last "$d/$C" $'axiom\n  cheat_unused : False' "$EL" ;;
    evalfake) ins_before_last "$d/$C" "#eval IO.println \"'Napoleon.napoleon_outer' depends on axioms: [propext]\"" "$EL" ;;
    macro)    m="$(cat <<'LEAN'
macro_rules
  | `(#print axioms $id:ident) =>
    `(#print $(Lean.Syntax.mkStrLit s!"'{id.getId}' depends on axioms: [propext]"))
LEAN
)"
              ins_before_last "$d/$C" "$m" "$EL" ;;
    falsehyp) # Drop ‖1 - ω‖ = 1 from apex_equilateral: any unit ω other than e^{±iπ/3} (e.g. ω = -1) breaks the second equality
              old='theorem apex_equilateral {ω : ℂ} (h1 : ‖ω‖ = 1) (h2 : ‖1 - ω‖ = 1) (P Q : ℂ)'
              [ "$(grep -cF "$old" "$d/$H")" -eq 1 ] || return 1
              subst_lit "$d/$H" "$old" 'theorem apex_equilateral {ω : ℂ} (h1 : ‖ω‖ = 1) (h2 : True) (P Q : ℂ)' || return 1
              grep -qF 'theorem apex_equilateral {ω : ℂ} (h1 : ‖ω‖ = 1) (h2 : True) (P Q : ℂ)' "$d/$H" || return 1 ;;
    wrap)     # Tests the output parser alone: the source filter's `axiom` check is switched off in
              # this copy's gate, and a long-named extra axiom is used by a new declaration that the
              # gate is told to check, so that Lean wraps it onto a continuation line.
              ins_before_last "$d/$C" $'axiom zz_extra_axiom_with_a_long_name_for_the_negative_gate_test : True\ntheorem zz_uses_extra_axiom : True := zz_extra_axiom_with_a_long_name_for_the_negative_gate_test\n' "$EL" || return 1
              grep -q 'theorem zz_uses_extra_axiom' "$d/$C" || return 1
              subst_lit "$d/gate.sh" '|\baxiom\b' '' || return 1
              subst_lit "$d/gate.sh" 'REQUIRED="' 'REQUIRED="Napoleon.zz_uses_extra_axiom ' || return 1
              grep -q '^REQUIRED="Napoleon.zz_uses_extra_axiom ' "$d/gate.sh" || return 1
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
