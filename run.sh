#!/bin/sh
# Runs Blend's executable, built first if stale (build.sh); paths
# are taken from where it is run.
#
#   run.sh show FILE.blend [--read|--objects|--resolve] [NAME]
#     a stage, the objects by default; what NAME resolves to, or with
#     --objects that object
#   run.sh emit [--alone] [--force] [--no-check|--verdict] FILE.blend...
#     writes each module's tree beside it, or with --alone the modules
#     named, leaving those current by their stamps as they are unless
#     --force: each .bend, its laws and proofs in it after its code;
#     prints each path, or the errors of any, writing none; then has
#     Bend check those holding laws
set -u
bin=$("$(dirname "$0")/build.sh") || exit 1
exec "$bin" "$@"
