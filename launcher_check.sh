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
got=$(BEND_HOME=$h "$b" --help 2>&1) || fail "--help fails"
[ "$(echo "$got" | head -n 1)" = "usage:" ] || fail "--help says '$got'"
BEND_HOME=$h "$b" update | grep -q "runs the checkout at $root" || fail "update names no checkout"
(cd samples && BEND_HOME=$h "$b" emit --alone choice.blend "$o/native" > /dev/null) || fail "a native emit fails"
cmp -s "$o/native/choice.bend" samples/choice.bend || fail "a native emit differs from samples/choice.bend"
(cd samples && BLEND_NATIVE=0 BEND_HOME=$h "$b" emit --alone choice.blend "$o/bend" > /dev/null) || fail "an emit through bend fails"
cmp -s "$o/bend/choice.bend" samples/choice.bend || fail "an emit through bend differs from samples/choice.bend"
BEND_HOME=$root/results/launcher/none "$b" version > /dev/null 2>&1 && fail "runs where it is not installed"
[ "$status" = 0 ] && echo "launcher: installed, version, --help, update, native and through bend: ok"
exit "$status"
