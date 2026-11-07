#!/bin/sh
# Blend's samples (README.md): each valid sample's .bend, what Blend
# emits from its .blend (a generated file, checked current by
# check_generated.sh), runs under Bend to print what its .out says; each
# invalid sample fails, its errors exactly its .err; each refused sample
# emits, and Bend, checking it as emit does, refuses its file, emit's
# errors exactly its .err (its laws, proofs and witnesses there,
# `blend-laws-in-module`; `blend-cli.checks`).
# Run by Blend's gate (check.sh).
#
#   samples/check.sh
set -u
cd "$(dirname "$0")" || exit 1
BLEND_ROOT=$(cd .. && pwd)
. "$BLEND_ROOT/tools.sh"
BEND=${BEND:-$(command -v bend || echo "$HOME/.bend/bin/bend")}
# emit checks with it (blend-cli.checks)
export BEND
CAPPED=$TOOLS/capped.sh
# Blend's executable, built once for each version of its sources
BLEND=$(BEND=$BEND ../build.sh) || { echo "blend: no executable to check with"; exit 1; }
status=0
n=0
for src in *.blend; do
  base=${src%.blend}
  n=$((n + 1))
  if [ ! -f "$base.bend" ] || [ ! -f "$base.out" ]; then
    echo "blend: $src has no $base.bend or $base.out"
    status=1
    continue
  fi
  got=$("$CAPPED" 1000 60 "$BEND" "$base.bend" 2>&1)
  if [ "$got" != "$(cat "$base.out")" ]; then
    echo "blend: $base.bend prints '$got', not '$(cat "$base.out")'"
    status=1
  fi
done
m=0
# an invalid sample that emits writes into results/ (out of git), never
# beside the sample
out=../results/invalid
mkdir -p "$out" || exit 1
for src in invalid/*.blend; do
  m=$((m + 1))
  err=${src%.blend}.err
  [ -f "$err" ] || { echo "blend: $src has no .err"; status=1; continue; }
  if got=$("$CAPPED" 500 30 "$BLEND" emit --alone "$src" "$out" 2>&1); then
    echo "blend: $src emits, where it must fail with $(cat "$err")"
    status=1
  elif [ "$got" != "$(cat "$err")" ]; then
    echo "blend: $src gives '$got', not '$(cat "$err")'"
    status=1
  fi
done
k=0
r=../results/refused
mkdir -p "$r" || exit 1
for src in refused/*.blend; do
  k=$((k + 1))
  base=${src#refused/}
  base=${base%.blend}
  [ -f "refused/$base.err" ] || { echo "blend: $src has no .err"; status=1; continue; }
  if got=$("$CAPPED" 1000 60 "$BLEND" emit --alone "$src" "$r" 2>&1 >"$r/$base.wrote"); then
    echo "blend: $src emits and passes its check, where Bend must refuse it"
    status=1
  elif [ "$(cat "$r/$base.wrote")" != "$r/$base.bend" ]; then
    echo "blend: $src writes '$(cat "$r/$base.wrote")', not $r/$base.bend"
    status=1
  elif [ "$got" != "$(cat "refused/$base.err")" ]; then
    echo "blend: emit of $src gives '$got', not '$(cat "refused/$base.err")'"
    status=1
  fi
done
# `--no-check` leaves the check to the run; `--verdict` asks the
# kernel's too, refused with it; the files checked, by a bend that logs
# them: a tree's root holding laws alone, its check covering what it
# imports, an import holding them where its root does not
"$CAPPED" 500 30 "$BLEND" emit --alone --no-check refused/law-false.blend "$r" >/dev/null 2>&1 ||
  { echo "blend: emit --no-check checks"; status=1; }
if "$CAPPED" 500 30 "$BLEND" emit --no-check --verdict laws.blend "$r" >/dev/null 2>&1; then
  echo "blend: emit takes --no-check with --verdict"
  status=1
fi
c=$(cd .. && pwd)/results/checks
mkdir -p "$c/lib" || exit 1
printf '#!/bin/sh\necho "$*" >> "%s"\n' "$c/bend.log" > "$c/bend" && chmod +x "$c/bend" || exit 1
cp refused/law-false.blend "$c/lib/" || exit 1
printf 'import Base\nimport ./lib/law-false.blend as F\n\nlaw two:\n  {Nat.add(1n, 1n) == 2n : Nat}\nproof two():\n  {==}\n' > "$c/root.blend" || exit 1
printf 'import Base\nimport ./lib/law-false.blend as F\n\ndef one() -> Nat:\n  1n\n' > "$c/plain.blend" || exit 1
: > "$c/bend.log"
(cd "$c" && BEND=$c/bend "$CAPPED" 500 30 "$BLEND" emit root.blend >/dev/null && BEND=$c/bend "$CAPPED" 500 30 "$BLEND" emit --verdict plain.blend >/dev/null &&
  BEND=$c/bend "$CAPPED" 500 30 "$BLEND" emit --alone --no-check root.blend >/dev/null) || { echo "blend: emit with a logging bend fails"; status=1; }
want="./root.bend --check-only
lib/law-false.bend --verdict"
[ "$(cat "$c/bend.log")" = "$want" ] || { echo "blend: emit checks '$(cat "$c/bend.log")', not '$want'"; status=1; }
# the import's false law through its root's check: once, its source line
# named from where blend runs
if got=$(cd "$c" && "$CAPPED" 1000 60 "$BLEND" emit root.blend 2>&1 >/dev/null); then
  echo "blend: a false law in an import passes its root's check"
  status=1
elif [ "$(echo "$got" | grep -c "^SOME PROOFS FAIL$")" != 1 ] || ! echo "$got" | grep -qx "Source: lib/law-false.blend:14"; then
  echo "blend: a false law in an import gives '$got'"
  status=1
fi
# `emit` writes a module's tree, the imports none names written too, a
# stale one made current; `--alone` writes the modules named, a stale
# import left as it is; a module named by its absolute path finds its
# imports (results/, fixed paths, overwritten each run;
# `blend-emit-verifies-imports`)
v=../results/verify
mkdir -p "$v/lib" || exit 1
cp imports.blend "$v/" && cp lib/shapes.blend "$v/lib/" && echo "# stale" > "$v/lib/shapes.bend" || exit 1
want="lib/shapes.bend
./imports.bend"
if ! got=$(cd "$v" && "$CAPPED" 500 30 "$BLEND" emit imports.blend 2>&1); then
  echo "blend: emit of a tree fails: $got"
  status=1
elif [ "$got" != "$want" ]; then
  echo "blend: emit of a tree writes '$got', not '$want'"
  status=1
elif ! cmp -s "$v/lib/shapes.bend" lib/shapes.bend || ! cmp -s "$v/imports.bend" imports.bend; then
  echo "blend: emit of a tree writes other than the samples' files"
  status=1
fi
# `deps`: the tree as emit writes it, imports first, each current
want="current lib/shapes.blend
current imports.blend"
got=$(cd "$v" && "$CAPPED" 500 30 "$BLEND" deps imports.blend 2>&1) || { echo "blend: deps of a current tree fails"; status=1; }
[ "$got" = "$want" ] || { echo "blend: deps of a current tree says '$got', not '$want'"; status=1; }
want="lib/shapes.bend: lib/shapes.blend
	blend emit --alone lib/shapes.blend

imports.bend: imports.blend lib/shapes.blend
	blend emit --alone imports.blend"
got=$(cd "$v" && "$CAPPED" 500 30 "$BLEND" deps --make imports.blend 2>&1) || { echo "blend: deps --make fails"; status=1; }
[ "$got" = "$want" ] || { echo "blend: deps --make says '$got', not '$want'"; status=1; }
echo "# stale" > "$v/lib/shapes.bend" || exit 1
(cd "$v" && "$CAPPED" 500 30 "$BLEND" emit --alone imports.blend >/dev/null) || { echo "blend: emit --alone fails"; status=1; }
[ "$(cat "$v/lib/shapes.bend")" = "# stale" ] || { echo "blend: emit --alone writes an import"; status=1; }
# a stale import, the status 1; a module with errors refused, the errors
# on standard error
want="stale lib/shapes.blend
current imports.blend"
if got=$(cd "$v" && "$CAPPED" 500 30 "$BLEND" deps imports.blend 2>&1); then
  echo "blend: deps of a stale tree succeeds"
  status=1
elif [ "$got" != "$want" ]; then
  echo "blend: deps of a stale tree says '$got', not '$want'"
  status=1
fi
if got=$(cd invalid && "$CAPPED" 500 30 "$BLEND" deps law-unproven.blend 2>/dev/null); then
  echo "blend: deps of a module with errors succeeds"
  status=1
elif [ "$got" != "refused law-unproven.blend" ]; then
  echo "blend: deps of a module with errors says '$got'"
  status=1
fi
mkdir -p ../results/absolute || exit 1
"$CAPPED" 500 30 "$BLEND" emit --alone "$PWD/imports.blend" ../results/absolute >/dev/null ||
  { echo "blend: a module named by its absolute path fails"; status=1; }
# `show`: what a name resolves to, its kind, the objects giving it, the
# final first, where it is written and its lines; a name of no
# definition refused
want="AnyOf.double (def): AnyOf < Monoid, laws.blend:60
  upd def double(+x: T()) -> T():
    x"
got=$("$CAPPED" 500 30 "$BLEND" show laws.blend AnyOf.double 2>&1) || { echo "blend: show of a name fails"; status=1; }
[ "$got" = "$want" ] || { echo "blend: show of a name says '$got', not '$want'"; status=1; }
if got=$("$CAPPED" 500 30 "$BLEND" show laws.blend Nope.x 2>&1); then
  echo "blend: show of no definition succeeds"
  status=1
elif [ "$got" != "blend: no definition Nope.x" ]; then
  echo "blend: show of no definition says '$got'"
  status=1
fi
# a tree into a directory: refused, its imports' paths kept
want="blend: a tree is written beside its modules, its imports' paths kept; into a directory, --alone writes the modules named"
if got=$("$CAPPED" 500 30 "$BLEND" emit imports.blend ../results/absolute 2>&1); then
  echo "blend: a tree into a directory is written"
  status=1
elif [ "$got" != "$want" ]; then
  echo "blend: a tree into a directory gives '$got', not '$want'"
  status=1
fi
# a path holding a newline would break the markers naming it: refused
nl="imports
.blend"
want="blend: a path holding a newline would break the lines naming it: refused"
if got=$("$CAPPED" 500 30 "$BLEND" emit "$nl" 2>&1); then
  echo "blend: a path holding a newline passes"
  status=1
elif [ "$got" != "$want" ]; then
  echo "blend: a path holding a newline gives '$got', not '$want'"
  status=1
fi
[ "$status" -eq 0 ] && echo "blend samples: $n valid, $m invalid, $k refused: ok"
exit "$status"
