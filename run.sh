#!/bin/sh
# Runs Blend's executable, built first if stale (build.sh); paths
# are taken from where it is run.
#
#   run.sh show FILE.blend [read|objects|resolve|NAME]   a stage, or what
#                                         NAME resolves to
#   run.sh emit [--alone] FILE.blend... [DIR]
#     writes each module's file beside it, or into DIR: its .bend, its
#     laws and proofs in it after its code; prints each path
#     written, or the errors of any, writing none. An import no argument
#     names is verified, its files as it would emit them, unless --alone
set -u
bin=$("$(dirname "$0")/build.sh") || exit 1
exec "$bin" "$@"
