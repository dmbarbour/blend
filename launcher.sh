#!/bin/sh
# `blend`, beside `bend` in $BEND_HOME/bin (blend-command-mirrors-bend):
# install.sh copies this there and names, in $BEND_HOME/blend/home, the
# checkout it runs. It runs the tool built natively from that checkout,
# built again when Blend or Bend changes (build.sh); where no native build
# can be made (no clang, or BLEND_NATIVE=0), `bend blend.bend --`, slower.
# Its own words: `version`, `rebuild`, `update`; a file first, it runs the
# module as `bend` runs a .bend; the rest go to the tool.
#
#   blend version    where it runs from, Blend's source hash, Bend's
#                    version, and whether natively or through Bend
#   blend rebuild    the tool built again
#   blend update     how to take a later Blend
#   blend FILE.blend [args]|-o OUT|--check-only|--verdict
#                    the module's tree emitted, then `bend FILE.bend` with
#                    the same arguments, the program's input, output and
#                    status its own; each error Bend reports on a line of
#                    the module's file followed by the .blend line it
#                    comes from, `Source: FILE.blend:LINE` (where.sh's
#                    rule)
#   blend ARGS...    the tool (blend --help)
set -u
home=${BEND_HOME:-$HOME/.bend}
cfg=$home/blend/home
[ -r "$cfg" ] || { echo "blend: not installed ($cfg is missing): run install.sh from a Blend checkout" >&2; exit 1; }
read -r kind src < "$cfg"
[ "$kind" = checkout ] || { echo "blend: $cfg names no checkout" >&2; exit 1; }
[ -f "$src/blend.bend" ] || { echo "blend: no blend.bend in $src, the checkout $cfg names" >&2; exit 1; }
bend=$(command -v bend 2>/dev/null || echo "$home/bin/bend")
[ -x "$bend" ] || { echo "blend: no bend (install Bend: curl -fsSL https://bend-lang.com/install.sh | sh)" >&2; exit 1; }
# a native build wants clang, which Bend's builds call from the path
native=1
[ "${BLEND_NATIVE:-1}" = 0 ] && native=0
command -v clang >/dev/null 2>&1 || native=0
hash() { { sha256sum "$1" 2>/dev/null || shasum -a 256 "$1"; } | cut -c1-8; }
case ${1:-} in
  version)
    at=$(git -C "$src" rev-parse --short HEAD 2>/dev/null) &&
      { [ -z "$(git -C "$src" status --porcelain -- blend.bend 2>/dev/null)" ] || at="$at, blend.bend changed"; }
    how="natively"; [ "$native" = 1 ] || how="through bend (no native build)"
    echo "blend from the checkout $src${at:+ ($at)}, blend.bend $(hash "$src/blend.bend"); $("$bend" version), $how"
    exit 0 ;;
  rebuild)
    [ "$native" = 1 ] || { echo "blend: no native build to make (no clang, or BLEND_NATIVE=0): blend runs through bend" >&2; exit 1; }
    BEND=$bend "$src/build.sh" --force >/dev/null || exit 1
    echo "blend: built again"
    exit 0 ;;
  update)
    echo "blend runs the checkout at $src: take a later Blend with git there (git -C $src pull); it builds again when its sources change"
    exit 0 ;;
esac
if [ "$native" = 1 ]; then
  exe=$(BEND=$bend "$src/build.sh") || { echo "blend: the native build failed; running through bend" >&2; native=0; }
fi
tool() {
  if [ "$native" = 1 ]; then "$exe" "$@"; else "$bend" "$src/blend.bend" -- "$@"; fi
}
# Bend's standard error, each line as it comes; after an error's excerpt
# whose marked line (` N>| `) is line N of the module's file, the .blend
# line it comes from: the nearest marker above, `# blend: FILE:LINE`, and
# the lines after it the source's next (where.sh)
map='
  FNR == NR {
    line[FNR] = $0; n = FNR
    if ($0 ~ /^# blend: /) { m = substr($0, 10); i = match(m, /:[0-9]+$/); mf[FNR] = substr(m, 1, i - 1); ms[FNR] = substr(m, i + 1) }
    next
  }
  pend != "" && $0 !~ /^ *[0-9]*[ >]\| / && $0 !~ /^ +\|/ { print "Source: " pend; pend = "" }
  { print; fflush() }
  /^ *[0-9]+>\| / {
    k = $0; sub(/^ */, "", k); num = k; sub(/>.*/, "", num); txt = k; sub(/^[0-9]+>\| /, "", txt); num += 0
    if (num <= n && line[num] == txt) {
      for (a = num; a > 0 && !(a in mf); a--) ;
      if (a > 0) { d = num - a - 1; if (d < 0) d = 0; pend = mf[a] ":" (ms[a] + d) }
    }
  }
  END { if (pend != "") print "Source: " pend }'
case ${1:-} in
  *.blend)
    file=$1
    shift
    tool emit "$file" > /dev/null || exit 1
    bf=${file%.blend}.bend
    exec 3>&1
    st=$({ { "$bend" "$bf" "$@" 2>&1 1>&3 3>&- 4>&-; echo $? >&4; } | awk "$map" "$bf" - >&2 3>&- 4>&-; } 4>&1)
    exec 3>&-
    exit "$st" ;;
esac
if [ "$native" = 1 ]; then exec "$exe" "$@"; fi
exec "$bend" "$src/blend.bend" -- "$@"
