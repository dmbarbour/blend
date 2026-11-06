#!/bin/sh
# Installs `blend` beside `bend`, in $BEND_HOME/bin (~/.bend/bin), running
# this checkout (blend-command-mirrors-bend, blend-cli.launcher): the
# launcher copied there, $BEND_HOME/blend/home naming the checkout, and the
# tool built natively where clang is found. Run again after moving the
# checkout; a release's installer is to come (blend-cli.install).
#
#   install.sh
set -eu
cd "$(dirname "$0")"
src=$PWD
home=${BEND_HOME:-$HOME/.bend}
bend=$(command -v bend 2>/dev/null || echo "$home/bin/bend")
[ -x "$bend" ] || { echo "install.sh: no bend: install Bend first (curl -fsSL https://bend-lang.com/install.sh | sh)" >&2; exit 1; }
case $src in *"
"*) echo "install.sh: the checkout's path holds a newline" >&2; exit 1 ;; esac
mkdir -p "$home/bin" "$home/blend"
cp launcher.sh "$home/bin/blend.new"
chmod +x "$home/bin/blend.new"
mv -f "$home/bin/blend.new" "$home/bin/blend"
printf 'checkout %s\n' "$src" > "$home/blend/home"
if command -v clang >/dev/null 2>&1; then
  BEND=$bend ./build.sh >/dev/null
else
  echo "install.sh: no clang: blend will run through bend, slower" >&2
fi
echo "blend installed at $home/bin/blend, running the checkout at $src"
"$home/bin/blend" version
