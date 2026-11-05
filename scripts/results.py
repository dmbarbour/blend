#!/usr/bin/env python3
"""The analysis store: bulk results and the parameters that produced them.

One SQLite file, results/analysis.sqlite (or $BLEND_RESULTS), kept out of
git. A run is one invocation of a tool: its parameters as JSON, the commit
it ran on and how many paths were changed, Bend's version, the CPU, a
note. Results hang off runs:
  counts   instructions per build and workload (bench/measure.sh: build
           `blend`, the family's shape its workload, its size its k)
  metrics  any named number (bench/measure.sh: each size's seconds)

    results.py run TOOL PARAMS_JSON [NOTE]       start a run, print its id
    results.py count RUN BUILD WORKLOAD K LAZY ITRS INSTRUCTIONS [CYCLES]
                                                 (ITRS empty where none)
    results.py metric RUN NAME VALUE
    results.py sql QUERY                         print rows, tab-separated

Run from anywhere in the repository; read the store with any SQLite client
(`results.py sql "select ..."`), e.g. to compare runs with one parameter
changed. Runs before Blend became a repository of its own, up to 281, are
in glam-in-bend's store (blend-own-repository).
"""

import datetime
import json
import os
import sqlite3
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DB = os.environ.get("BLEND_RESULTS", os.path.join(ROOT, "results", "analysis.sqlite"))

SCHEMA = """
create table if not exists runs (
  id integer primary key, at text not null, tool text not null, params text not null,
  git_commit text, git_changed integer, bend text, cpu text, note text);
create table if not exists counts (
  run_id integer not null references runs(id), build text not null, workload text not null,
  k integer not null, lazy integer not null, interactions integer, instructions integer, cycles integer);
create table if not exists metrics (
  run_id integer not null references runs(id), name text not null, value real);
"""


def db():
    os.makedirs(os.path.dirname(DB), exist_ok=True)
    c = sqlite3.connect(DB)
    c.executescript(SCHEMA)
    return c


def sh(*args):
    try:
        return subprocess.run(args, cwd=ROOT, capture_output=True, text=True, timeout=30).stdout.strip()
    except (OSError, subprocess.SubprocessError):
        return None


def cpu():
    try:
        for line in open("/proc/cpuinfo"):
            if line.startswith("model name"):
                return line.split(":", 1)[1].strip()
    except OSError:
        pass
    return None


def cmd_run(tool, params, note=None):
    json.loads(params)
    status = sh("git", "status", "--porcelain")
    bend = sh(os.environ.get("BEND", "bend"), "version")
    with db() as c:
        cur = c.execute(
            "insert into runs (at, tool, params, git_commit, git_changed, bend, cpu, note) values (?,?,?,?,?,?,?,?)",
            (datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"), tool, params,
             sh("git", "rev-parse", "--short", "HEAD"), len(status.splitlines()) if status is not None else None,
             bend, cpu(), note))
        print(cur.lastrowid)


def num(s):
    return None if s is None or s == "" else int(s)


def cmd_count(run, build, workload, k, lazy, itrs, ins, cycles=None):
    with db() as c:
        c.execute("insert into counts values (?,?,?,?,?,?,?,?)",
                  (int(run), build, workload, int(k), int(lazy), num(itrs), num(ins), num(cycles)))


def cmd_metric(run, name, value):
    with db() as c:
        c.execute("insert into metrics values (?,?,?)", (int(run), name, float(value)))


def cmd_sql(query):
    with db() as c:
        cur = c.execute(query)
        if cur.description:
            print("\t".join(d[0] for d in cur.description))
        for row in cur:
            print("\t".join("" if x is None else str(x) for x in row))


def main(argv):
    cmds = {"run": cmd_run, "count": cmd_count, "metric": cmd_metric, "sql": cmd_sql}
    if not argv or argv[0] not in cmds:
        print(__doc__.strip())
        return 2
    cmds[argv[0]](*argv[1:])
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
