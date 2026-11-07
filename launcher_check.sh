#!/bin/sh
# The launcher (launcher.sh, install.sh; blend-cli.launcher): installed
# into a home of its own under results/ (out of git, never the user's
# ~/.bend), it says where it runs from, answers --help, emits a sample
# natively and through bend (BLEND_NATIVE=0) as the sample's .bend is,
# and refuses where it is not installed. Run by Blend's gate (check.sh).
#
#   launcher_check.sh
set -u
cd "$(dirname "$0")" || exit 1
root=$PWD
BLEND_ROOT=$root
. ./tools.sh
h=$root/results/launcher/home
o=$root/results/launcher/out
mkdir -p "$h" "$o/native" "$o/bend" "$root/results/launcher/none" || exit 1
status=0
fail() { echo "launcher: $*"; status=1; }
BEND_HOME=$h sh install.sh > "$o/install.txt" 2>&1 || fail "install.sh fails: $(cat "$o/install.txt")"
b=$h/bin/blend
case $(BEND_HOME=$h "$b" version 2>&1) in
  "blend from the checkout $root"*) ;;
  *) fail "version says '$(BEND_HOME=$h "$b" version 2>&1)'" ;;
esac
# the version stamp version reports, as the tool has it
vs=$(BEND_HOME=$h "$b" --version-stamp) || fail "--version-stamp fails"
case $(BEND_HOME=$h "$b" version 2>&1) in
  *", version stamp $vs; "*) ;;
  *) fail "version names a version stamp other than the tool's, $vs: $(BEND_HOME=$h "$b" version 2>&1)" ;;
esac
got=$(BEND_HOME=$h "$b" --help 2>&1) || fail "--help fails"
[ "$(echo "$got" | head -n 1)" = "usage:" ] || fail "--help says '$got'"
BEND_HOME=$h "$b" update | grep -q "runs the checkout at $root" || fail "update names no checkout"
[ "$(BEND_HOME=$h "$b" guide | head -n 1)" = "# The Blend guide" ] || fail "guide prints no guide"
cp samples/choice.blend "$o/native/" && cp samples/choice.blend "$o/bend/" || exit 1
# forced, so that a file an earlier run left proves nothing
(cd "$o/native" && BEND_HOME=$h "$b" emit --alone --force choice.blend > /dev/null) || fail "a native emit fails"
cmp -s "$o/native/choice.bend" samples/choice.bend || fail "a native emit differs from samples/choice.bend"
(cd "$o/bend" && BLEND_NATIVE=0 BEND_HOME=$h "$b" emit --alone --force choice.blend > /dev/null) || fail "an emit through bend fails"
cmp -s "$o/bend/choice.bend" samples/choice.bend || fail "an emit through bend differs from samples/choice.bend"
BEND_HOME=$root/results/launcher/none "$b" version > /dev/null 2>&1 && fail "runs where it is not installed"
# a file first: the module run as `bend` runs it, its output and status
# its own; an error on the module's file followed by its .blend line
r=$root/results/launcher/run
mkdir -p "$r" || exit 1
cp samples/choice.blend samples/refused/declare-misfit.blend "$r/" || exit 1
got=$(cd "$r" && BEND_HOME=$h "$b" choice.blend 2>&1) || fail "a run of choice.blend fails: $got"
[ "$got" = "$(cat samples/choice.out)" ] || fail "a run of choice.blend prints '$got'"
if got=$(cd "$r" && BEND_HOME=$h "$b" declare-misfit.blend --check-only 2>&1); then
  fail "a misfit passes its check"
else
  echo "$got" | grep -qx "Source: declare-misfit.blend:8" || fail "a misfit's error names no source line: $got"
fi
# emit's own check, with the launcher's bend: the misfit's error and its
# source line, once, the status 1
if got=$(cd "$r" && BEND_HOME=$h "$b" emit declare-misfit.blend 2>&1 >/dev/null); then
  fail "emit of a misfit passes its check"
elif [ "$(echo "$got" | grep -c "^Source: declare-misfit.blend:8$")" != 1 ]; then
  fail "emit of a misfit names its source line other than once: $got"
fi
# and through bend, where no native build is made (Process.run and
# IO.get_env on Bend's JavaScript lane)
if got=$(cd "$r" && BLEND_NATIVE=0 BEND_HOME=$h "$b" emit declare-misfit.blend 2>&1 >/dev/null); then
  fail "emit through bend of a misfit passes its check"
elif [ "$(echo "$got" | grep -c "^Source: declare-misfit.blend:8$")" != 1 ]; then
  fail "emit through bend of a misfit names its source line other than once: $got"
fi
# an error in an imported module's file, named from where blend runs
mkdir -p "$r/imp/lib" || exit 1
printf 'import Base\n\nobject Bad with\n  def f(+n: U32) -> U32:\n    Nat.add(n, 1n)\n' > "$r/imp/lib/bad.blend" || exit 1
printf 'import Base\nimport ./lib/bad.blend as B\n\ndef main() -> IO(Unit):\n  IO.print(U32.show(B.Bad.f(1)))\n' > "$r/imp/root.blend" || exit 1
if got=$(cd "$r" && BEND_HOME=$h "$b" imp/root.blend 2>&1); then
  fail "an imported module's error passes"
else
  echo "$got" | grep -qx "Source: imp/lib/bad.blend:5" || fail "an imported module's error names no source line: $got"
fi
[ "$status" = 0 ] && echo "launcher: installed, version, its version stamp, --help, update, guide, native and through bend, a run, an error's source, emit's check natively and through bend, an import's: ok"
exit "$status"
